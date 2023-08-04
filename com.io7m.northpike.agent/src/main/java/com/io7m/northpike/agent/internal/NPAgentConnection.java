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


package com.io7m.northpike.agent.internal;

import com.io7m.jattribute.core.AttributeReadableType;
import com.io7m.jattribute.core.AttributeType;
import com.io7m.jattribute.core.Attributes;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentConnectionStatus;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAEventType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Executors;
import java.util.concurrent.Flow;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.SubmissionPublisher;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.AUTHENTICATED;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.AUTHENTICATING;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.AUTHENTICATION_FAILED;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTED;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTING;
import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTION_FAILED;
import static com.io7m.northpike.agent.internal.NPAgentExceptions.errorUnexpectedMessage;

/**
 * A durable agent connection.
 */

public final class NPAgentConnection implements NPAgentConnectionType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentConnection.class);

  private final NPAgentConfiguration configuration;
  private final CloseableCollectionType<NPAgentException> resources;
  private final AtomicBoolean closed;
  private final LinkedBlockingQueue<NPSendQueueElementType> sendQueue;
  private final HashMap<UUID, NPCommandAwaitingResponse> sentCommands;
  private final LinkedBlockingQueue<NPAMessageType> receiveQueue;
  private final AttributeType<NPAgentConnectionStatus> status;
  private final SubmissionPublisher<NPAgentException> exceptions;
  private volatile NPAgentConnectionHandlerType handler;

  private NPAgentConnection(
    final NPAgentConfiguration inConfiguration,
    final CloseableCollectionType<NPAgentException> inResources)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.closed =
      new AtomicBoolean(false);

    this.sendQueue =
      new LinkedBlockingQueue<>();
    this.sentCommands =
      new HashMap<>();
    this.receiveQueue =
      new LinkedBlockingQueue<>();
    this.exceptions =
      new SubmissionPublisher<>();

    this.status =
      Attributes.create(e -> LOG.error("Event handling error: ", e))
        .create(CONNECTING);

    this.status.subscribe((oldValue, newValue) -> {
      LOG.debug("Agent connection {} -> {}", oldValue, newValue);
    });
  }

  /**
   * Open a connection to the server.
   *
   * @param configuration The agent configuration
   *
   * @return The connection
   */

  public static NPAgentConnectionType open(
    final NPAgentConfiguration configuration)
  {
    final var resources =
      CloseableCollection.create(() -> new NPAgentException(
        "One or more resources could not be closed.",
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      ));

    final var executor =
      Executors.newSingleThreadExecutor(runnable -> {
        final var t = new Thread(runnable);
        t.setName(
          "com.io7m.northpike.agent.connection[%d]"
            .formatted(Long.valueOf(t.getId()))
        );
        return t;
      });

    resources.add(executor::shutdown);

    final var connection =
      new NPAgentConnection(configuration, resources);

    executor.execute(connection::start);
    return connection;
  }

  private void start()
  {
    while (!this.closed.get()) {
      try {
        this.reconnect();
      } catch (final NPAgentException e) {
        LOG.warn("Pausing for reconnection.");
        try {
          Thread.sleep(1_000L);
        } catch (final InterruptedException ex) {
          Thread.currentThread().interrupt();
        }
        continue;
      }
      this.runLoop();
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
      } catch (final NPAgentException e) {
        this.status.set(CONNECTION_FAILED);
        this.exceptions.submit(e);
      }
    }
  }

  private void reconnect()
    throws NPAgentException
  {
    this.status.set(CONNECTING);
    LOG.info(
      "Connecting to {}:{}",
      this.configuration.remoteAddress(),
      this.configuration.remotePort()
    );

    final NPAgentConnectionHandlerType newHandler;
    final var strings = this.configuration.strings();
    try {
      newHandler = NPAgentConnectionHandlers.openConnection(this.configuration);
    } catch (final IOException e) {
      this.status.set(CONNECTION_FAILED);
      throw NPAgentExceptions.errorIO(strings, e);
    }

    this.resources.add(newHandler);
    this.status.set(CONNECTED);

    final var oldHandler = this.handler;
    this.handler = newHandler;

    try {
      if (oldHandler != null) {
        oldHandler.close();
      }
    } catch (final NPAgentException e) {
      LOG.warn("Unable to close old connection: ", e);
      this.exceptions.submit(e);
    }

    this.status.set(AUTHENTICATING);
    this.handler.send(NPACommandCLogin.of(this.configuration.accessKey()));

    while (!this.closed.get()) {
      final var responseOpt = this.handler.receive();
      if (responseOpt.isPresent()) {
        final var response = responseOpt.get();
        if (response instanceof final NPAResponseError error) {
          this.status.set(AUTHENTICATION_FAILED);
          throw new NPAgentException(
            error.message(),
            error.errorCode(),
            error.attributes(),
            Optional.empty()
          );
        }

        if (response instanceof NPAResponseOK) {
          this.status.set(AUTHENTICATED);
          return;
        }

        this.status.set(AUTHENTICATION_FAILED);
        throw errorUnexpectedMessage(strings, NPAResponseOK.class, response);
      }
    }
  }

  private void readPendingMessage()
    throws NPAgentException
  {
    final var messageOpt = this.handler.receive();
    if (messageOpt.isEmpty()) {
      return;
    }

    final var message = messageOpt.get();
    this.receiveQueue.add(message);

    if (message instanceof final NPAResponseType response) {
      final var command =
        this.sentCommands.get(response.correlationID());

      command.future.complete(response);
      return;
    }
  }

  private void sendPendingMessage()
    throws InterruptedException
  {
    final var toSend =
      this.sendQueue.poll(1L, TimeUnit.MILLISECONDS);

    if (toSend != null) {
      if (toSend instanceof final NPCommandAwaitingResponse command) {
        this.sentCommands.put(
          command.message.messageID(),
          command
        );

        try {
          this.handler.send(toSend.message());
        } catch (final NPAgentException e) {
          this.exceptions.submit(e);
          this.sentCommands.remove(toSend.message().messageID());
          command.future.completeExceptionally(e);
        }
      }

      if (toSend instanceof final NPNonCommandMessage message) {
        try {
          this.handler.send(toSend.message());
          message.future.complete(null);
        } catch (final NPAgentException e) {
          this.exceptions.submit(e);
          message.future.completeExceptionally(e);
        }
      }
    }
  }

  @Override
  public AttributeReadableType<NPAgentConnectionStatus> status()
  {
    return this.status;
  }

  @Override
  public <R extends NPAResponseType> CompletableFuture<R> submitCommand(
    final NPACommandType<R> command)
  {
    final var awaiting =
      new NPCommandAwaitingResponse(command, new CompletableFuture<>());
    this.sendQueue.add(awaiting);
    return (CompletableFuture<R>) (Object) awaiting.future;
  }

  @Override
  public CompletableFuture<Void> submitResponse(
    final NPAResponseType response)
  {
    final var awaiting =
      new NPNonCommandMessage(response, new CompletableFuture<>());
    this.sendQueue.add(awaiting);
    return awaiting.future;
  }

  @Override
  public CompletableFuture<Void> submitEvent(
    final NPAEventType event)
  {
    final var awaiting =
      new NPNonCommandMessage(event, new CompletableFuture<>());
    this.sendQueue.add(awaiting);
    return awaiting.future;
  }

  @Override
  public List<NPAMessageType> takeReceivedMessages()
  {
    final var results =
      new ArrayList<NPAMessageType>(this.receiveQueue.size());

    while (!this.receiveQueue.isEmpty()) {
      final var m = this.receiveQueue.poll();
      results.add(m);
    }

    return List.copyOf(results);
  }

  @Override
  public Flow.Publisher<NPAgentException> exceptions()
  {
    return this.exceptions;
  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }

  sealed interface NPSendQueueElementType
  {
    NPAMessageType message();
  }

  private record NPCommandAwaitingResponse(
    NPACommandType<?> message,
    CompletableFuture<Object> future)
    implements NPSendQueueElementType
  {

  }

  private record NPNonCommandMessage(
    NPAMessageType message,
    CompletableFuture<Void> future)
    implements NPSendQueueElementType
  {

  }
}
