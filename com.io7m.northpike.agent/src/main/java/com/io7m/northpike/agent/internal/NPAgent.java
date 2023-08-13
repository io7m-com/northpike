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
import com.io7m.northpike.agent.api.NPAgentType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandS2CType;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Flow;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.agent.api.NPAgentConnectionStatus.CONNECTING;

/**
 * A basic agent.
 */

public final class NPAgent implements NPAgentType,
  Flow.Subscriber<NPException>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgent.class);

  private final NPAgentConfiguration configuration;
  private final AtomicBoolean running;
  private CloseableCollectionType<NPAgentException> resources;
  private ThreadPoolExecutor buildExecutor;
  private ThreadPoolExecutor mainExecutor;
  private AttributeType<NPAgentConnectionStatus> connectionStatus;
  private Flow.Subscription subscription;

  private NPAgent(
    final NPAgentConfiguration inConfiguration)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.running =
      new AtomicBoolean(false);
    this.connectionStatus =
      Attributes.create(throwable -> {
        LOG.error("Exception raised during event handling: ", throwable);
      }).create(CONNECTING);
  }

  /**
   * A basic agent.
   *
   * @param configuration The configuration
   *
   * @return An agent
   */

  public static NPAgentType open(
    final NPAgentConfiguration configuration)
  {
    return new NPAgent(configuration);
  }

  @Override
  public void start()
    throws InterruptedException
  {
    if (this.running.compareAndSet(false, true)) {
      this.resources =
        CloseableCollection.create(() -> new NPAgentException(
          "One or more resources could not be closed.",
          new NPErrorCode("resources"),
          Map.of(),
          Optional.empty()
        ));

      this.buildExecutor =
        new ThreadPoolExecutor(
          1,
          1,
          1L,
          TimeUnit.SECONDS,
          new LinkedBlockingQueue<>(),
          runnable -> {
            final var t = new Thread(runnable);
            t.setName(
              "com.io7m.northpike.agent.build[%d]"
                .formatted(Long.valueOf(t.getId()))
            );
            return t;
          }
        );
      this.resources.add(this.buildExecutor::shutdown);

      this.mainExecutor =
        new ThreadPoolExecutor(
          1,
          1,
          1L,
          TimeUnit.SECONDS,
          new LinkedBlockingQueue<>(),
          runnable -> {
            final var t = new Thread(runnable);
            t.setName(
              "com.io7m.northpike.agent.main[%d]"
                .formatted(Long.valueOf(t.getId()))
            );
            return t;
          }
        );
      this.resources.add(this.mainExecutor::shutdown);

      final var bootLatch = new CountDownLatch(1);
      this.mainExecutor.execute(() -> {
        bootLatch.countDown();
        this.run();
      });
      bootLatch.await();
    }
  }

  @Override
  public void stop()
    throws NPAgentException
  {
    if (this.running.compareAndSet(true, false)) {
      this.resources.close();
    }
  }

  @Override
  public AttributeReadableType<NPAgentConnectionStatus> connectionStatus()
  {
    return this.connectionStatus;
  }

  private void run()
  {
    try (var connection = new NPAgentConnection(this.configuration)) {
      connection.exceptions()
        .subscribe(this);

      this.resources.add(
        connection.status()
          .subscribe((oldValue, newValue) -> {
            this.connectionStatus.set(newValue);
          })
      );

      runSendEnvironmentInfo(connection);
      while (this.running.get()) {
        runHandleMessages(connection);
      }
    } catch (final NPException e) {
      LOG.warn("Closing connection: ", e);
    }
  }

  private static void runHandleMessages(
    final NPAgentConnectionType connection)
  {
    final var messages =
      connection.takeReceivedMessages();

    for (final var message : messages) {
      runHandleMessage(connection, message);
    }
  }

  private static void runSendEnvironmentInfo(
    final NPAgentConnectionType connection)
  {
    LOG.debug("Sending environment information.");
    connection.submitCommand(NPACommandCEnvironmentInfo.of())
      .handle((r, throwable) -> {
        if (throwable != null) {
          LOG.error("Failed to send environment information: ", throwable);
        }
        return r;
      });
  }

  private static void runHandleMessage(
    final NPAgentConnectionType connection,
    final NPAMessageType message)
  {
    if (message instanceof final NPACommandS2CType<?> s2c) {
      runHandleS2CCommand(connection, s2c);
      return;
    }
  }

  private static void runHandleS2CCommand(
    final NPAgentConnectionType connection,
    final NPACommandS2CType<?> s2c)
  {
    if (s2c instanceof final NPACommandSLatencyCheck c) {
      runHandleCommandLatencyCheck(connection, c);
      return;
    }
  }

  private static void runHandleCommandLatencyCheck(
    final NPAgentConnectionType connection,
    final NPACommandSLatencyCheck c)
  {
    LOG.debug("Responding to latency check.");
    connection.submitResponse(
      new NPAResponseLatencyCheck(
        UUID.randomUUID(),
        c.messageID(),
        c.timeCurrent(),
        OffsetDateTime.now()
      )
    );
  }

  @Override
  public void close()
    throws NPAgentException
  {
    this.stop();
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription newSubscription)
  {
    this.subscription = newSubscription;
    this.resources.add(newSubscription::cancel);
    newSubscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPException item)
  {
    LOG.error("Connection raised exception: ", item);
  }

  @Override
  public void onError(
    final Throwable throwable)
  {
    LOG.error("Event handling exception: ", throwable);
  }

  @Override
  public void onComplete()
  {
    this.subscription.cancel();
  }
}
