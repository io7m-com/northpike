/*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

package com.io7m.northpike.connections;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.model.NPException;
import org.slf4j.Logger;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Flow;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.SubmissionPublisher;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * A durable connection.
 *
 * @param <M> The type of messages
 * @param <R> The type of responses
 */

public abstract class NPMessageConnectionAbstract<M, R extends M>
  implements NPMessageConnectionType<M, R>
{
  private final CloseableCollectionType<NPException> resources;
  private final AtomicBoolean closed;
  private final LinkedBlockingQueue<AwaitingResponse<M, ?>> sendQueue;
  private final LinkedBlockingQueue<M> receiveQueue;
  private final SubmissionPublisher<NPException> exceptions;
  private final NPMessageCorrelator<M, R> messageCorrelator;
  private final Logger logger;
  private final ExecutorService executor;
  private NPMessageHandlerType<M> handler;

  protected NPMessageConnectionAbstract(
    final Logger inLogger,
    final CloseableCollectionType<NPException> inResources)
  {
    this.logger =
      Objects.requireNonNull(inLogger, "inLogger");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.closed =
      new AtomicBoolean(false);

    this.sendQueue =
      new LinkedBlockingQueue<>();
    this.messageCorrelator =
      this.resources.add(
        new NPMessageCorrelator<>(
          this::onFindMessageID,
          this::onFindCorrelationID
        )
      );
    this.receiveQueue =
      new LinkedBlockingQueue<>();
    this.exceptions =
      new SubmissionPublisher<>();

    this.executor =
      Executors.newSingleThreadExecutor(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.northpike.connection[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    this.resources.add(this.executor::shutdown);
    this.executor.execute(this::start);
  }

  protected final NPMessageHandlerType<M> existingHandler()
  {
    return this.handler;
  }

  protected final boolean isClosed()
  {
    return this.closed.get();
  }

  protected final CloseableCollectionType<NPException> resources()
  {
    return this.resources;
  }

  protected final SubmissionPublisher<NPException> exceptionsPublisher()
  {
    return this.exceptions;
  }

  @Override
  public final CompletableFuture<R> submitExpectingResponse(
    final M message)
  {
    final var future =
      this.messageCorrelator.onSend(message);

    this.sendQueue.add(
      new AwaitingResponse<>(message, new CompletableFuture<>())
    );

    return (CompletableFuture<R>) future;
  }

  @Override
  public final void submitExpectingNoResponse(
    final M message)
  {
    final var awaiting =
      new AwaitingResponse<>(message, new CompletableFuture<Void>());

    this.sendQueue.add(awaiting);
    try {
      awaiting.future.get();
    } catch (final Exception e) {
      this.logger.debug("submitExpectingNoResponse: ", e);
    }
  }

  @Override
  public final List<M> takeReceivedMessages()
  {
    final var results = new ArrayList<M>(this.receiveQueue.size());
    while (!this.receiveQueue.isEmpty()) {
      final var m = this.receiveQueue.poll();
      results.add(m);
    }
    return List.copyOf(results);
  }

  @Override
  public final Optional<M> peekReceivedMessage()
  {
    return Optional.ofNullable(this.receiveQueue.peek());
  }

  @Override
  public final Optional<M> takeReceivedMessage()
  {
    return Optional.ofNullable(this.receiveQueue.poll());
  }

  @Override
  public final Flow.Publisher<NPException> exceptions()
  {
    return this.exceptions;
  }

  protected abstract UUID onFindMessageID(M message);

  protected abstract UUID onFindCorrelationID(R message);

  protected abstract NPMessageHandlerType<M> onConnect()
    throws NPException;

  protected abstract R onCheckIfMessageIsResponse(M message);

  private void start()
  {
    while (!this.closed.get()) {
      try {
        this.handler = this.onConnect();
      } catch (final Exception e) {
        this.logger.warn("Pausing for reconnection.");
        pauseBriefly();
        continue;
      }
      this.runLoop();
    }
  }

  private static void pauseBriefly()
  {
    try {
      Thread.sleep(250L);
    } catch (final InterruptedException ex) {
      Thread.currentThread().interrupt();
    }
  }

  private void runLoop()
  {
    while (!this.closed.get()) {
      try {
        this.sendPendingMessage();
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }

      try {
        this.readPendingMessage();
      } catch (final NPException e) {
        this.exceptions.submit(e);
      }
    }
  }

  private void readPendingMessage()
    throws NPException
  {
    final var messageOpt = this.handler.receive();
    if (messageOpt.isEmpty()) {
      return;
    }

    final var message =
      messageOpt.get();
    final var response =
      this.onCheckIfMessageIsResponse(message);

    if (response != null) {
      this.messageCorrelator.onReceive(response);
    } else {
      this.receiveQueue.add(message);
    }
  }

  private void sendPendingMessage()
    throws InterruptedException
  {
    final var toSend =
      this.sendQueue.poll(1L, TimeUnit.MILLISECONDS);

    if (toSend != null) {
      try {
        this.handler.send(toSend.message());
        toSend.future.complete(null);
      } catch (final NPException e) {
        this.exceptions.submit(e);
        toSend.future.completeExceptionally(e);
      }
    }
  }

  @Override
  public final void close()
    throws NPException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }

  private record AwaitingResponse<M, T>(
    M message,
    CompletableFuture<T> future)
  {

  }
}
