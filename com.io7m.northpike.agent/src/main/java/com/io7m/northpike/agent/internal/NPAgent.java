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

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.api.NPAgentType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandS2CType;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.strings.NPStrings;
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

/**
 * A basic agent.
 */

public final class NPAgent implements NPAgentType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgent.class);

  private volatile NPAgentConfiguration configuration;
  private final AtomicBoolean closed;
  private final NPStrings strings;
  private final CloseableCollectionType<NPAgentException> resources;

  private NPAgent(
    final NPAgentConfiguration inConfiguration,
    final NPStrings inStrings,
    final CloseableCollectionType<NPAgentException> inResources)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.closed =
      new AtomicBoolean(true);
  }

  /**
   * A basic agent.
   *
   * @param strings       The strings
   * @param configuration The configuration
   *
   * @return An agent
   *
   * @throws InterruptedException On interruption
   */

  public static NPAgentType open(
    final NPStrings strings,
    final NPAgentConfiguration configuration)
    throws InterruptedException
  {
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(configuration, "configuration");

    final var resources =
      CloseableCollection.create(() -> new NPAgentException(
        "One or more resources could not be closed.",
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      ));

    final var agent =
      new NPAgent(configuration, strings, resources);

    final var mainExecutor =
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
    resources.add(mainExecutor::shutdown);

    final var bootLatch = new CountDownLatch(1);
    mainExecutor.execute(() -> agent.run(bootLatch));
    bootLatch.await();
    return agent;
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

  private void run(
    final CountDownLatch bootLatch)
  {
    bootLatch.countDown();

    while (!this.isClosed()) {
      try (var connection =
             NPAgentConnection.open(this.strings, this.configuration)) {
        runSendEnvironmentInfo(connection);

        while (!this.isClosed()) {
          runHandleMessages(connection);
        }
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      } catch (final NPException | IOException e) {
        LOG.error("", e);
      }
    }
  }

  @Override
  public void setConfiguration(
    final NPAgentConfiguration agentConfiguration)
  {

  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
