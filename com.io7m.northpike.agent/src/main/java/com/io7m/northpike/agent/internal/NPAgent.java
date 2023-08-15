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
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.api.NPAgentStatus;
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

import java.io.IOException;
import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTED;
import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTING;
import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTION_FAILED;

/**
 * A basic agent.
 */

public final class NPAgent implements NPAgentType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgent.class);

  private final NPAgentConfiguration configuration;
  private final AtomicBoolean closed;
  private CloseableCollectionType<NPAgentException> resources;
  private ThreadPoolExecutor buildExecutor;
  private ThreadPoolExecutor mainExecutor;
  private AttributeType<NPAgentStatus> status;

  private NPAgent(
    final NPAgentConfiguration inConfiguration)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.closed =
      new AtomicBoolean(true);
    this.status =
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

  private static void runHandleMessages(
    final NPAgentConnectionType connection)
    throws InterruptedException, NPException, IOException
  {
    while (true) {
      final var messageOpt = connection.read();
      if (messageOpt.isPresent()) {
        runHandleMessage(connection, messageOpt.get());
      } else {
        break;
      }
    }
  }

  private static void runSendEnvironmentInfo(
    final NPAgentConnectionType connection)
    throws InterruptedException, NPException, IOException
  {
    LOG.debug("Sending environment information.");
    connection.ask(NPACommandCEnvironmentInfo.of());
  }

  private static void runHandleMessage(
    final NPAgentConnectionType connection,
    final NPAMessageType message)
    throws InterruptedException, NPException, IOException
  {
    if (message instanceof final NPACommandS2CType<?> s2c) {
      runHandleS2CCommand(connection, s2c);
      return;
    }
  }

  private static void runHandleS2CCommand(
    final NPAgentConnectionType connection,
    final NPACommandS2CType<?> s2c)
    throws InterruptedException, NPException, IOException
  {
    if (s2c instanceof final NPACommandSLatencyCheck c) {
      runHandleCommandLatencyCheck(connection, c);
      return;
    }
  }

  private static void runHandleCommandLatencyCheck(
    final NPAgentConnectionType connection,
    final NPACommandSLatencyCheck c)
    throws InterruptedException, NPException, IOException
  {
    LOG.debug("Responding to latency check.");
    connection.send(
      new NPAResponseLatencyCheck(
        UUID.randomUUID(),
        c.messageID(),
        c.timeCurrent(),
        OffsetDateTime.now()
      )
    );
  }

  @Override
  public void start()
    throws InterruptedException
  {
    if (this.closed.compareAndSet(true, false)) {
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
      this.mainExecutor.execute(() -> this.run(bootLatch));
      bootLatch.await();
    }
  }

  @Override
  public void stop()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }

  @Override
  public AttributeReadableType<NPAgentStatus> status()
  {
    return this.status;
  }

  private void run(
    final CountDownLatch bootLatch)
  {
    bootLatch.countDown();

    while (!this.isClosed()) {
      this.status.set(CONNECTING);

      try (var connection = NPAgentConnection.open(this.configuration)) {
        this.status.set(CONNECTED);
        runSendEnvironmentInfo(connection);

        while (!this.isClosed()) {
          runHandleMessages(connection);
        }
      } catch (final InterruptedException e) {
        this.status.set(CONNECTION_FAILED);
        Thread.currentThread().interrupt();
      } catch (final NPException | IOException e) {
        this.status.set(CONNECTION_FAILED);
        LOG.error("", e);
      }
    }
  }

  @Override
  public void close()
    throws NPAgentException
  {
    this.stop();
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
