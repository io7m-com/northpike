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


package com.io7m.northpike.agent.internal.worker;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.internal.NPAgentTaskType;
import com.io7m.northpike.agent.internal.connection.NPAgentConnection;
import com.io7m.northpike.agent.internal.connection.NPAgentConnectionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairType;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.protocol.agent.NPACommandC2SType;
import com.io7m.northpike.protocol.agent.NPACommandS2CType;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPACommandSWorkOffered;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAEventType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.protocol.agent.NPAResponseWorkOffered;
import com.io7m.northpike.protocol.agent.NPAResponseWorkSent;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The task that handles messaging for the agent.
 */

public final class NPAgentWorkerTaskMessaging implements NPAgentTaskType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentWorkerTaskMessaging.class);

  private final AtomicBoolean closed;
  private final NPTLSContextServiceType tlsContexts;
  private final NPAgentKeyPairType keyPair;
  private final NPStrings strings;
  private final CloseableCollectionType<NPAgentException> resources;
  private final NPAgentServerDescription configuration;
  private NPAgentConnectionType connection;

  private NPAgentWorkerTaskMessaging(
    final NPTLSContextServiceType inTlsContexts,
    final NPAgentKeyPairType inKeyPair,
    final NPStrings inStrings,
    final CloseableCollectionType<NPAgentException> inResources,
    final NPAgentServerDescription inConfiguration)
  {
    this.tlsContexts =
      Objects.requireNonNull(inTlsContexts, "tlsContexts");
    this.keyPair =
      Objects.requireNonNull(inKeyPair, "keyPair");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.closed =
      new AtomicBoolean(false);
  }

  /**
   * The task that handles messaging for the agent.
   *
   * @param strings       The strings
   * @param keyPair       The key pair
   * @param tlsContexts   The TLS context service
   * @param configuration The configuration
   *
   * @return An agent
   *
   * @throws InterruptedException On interruption
   */

  public static NPAgentWorkerTaskMessaging open(
    final NPStrings strings,
    final NPTLSContextServiceType tlsContexts,
    final NPAgentKeyPairType keyPair,
    final NPAgentServerDescription configuration)
    throws InterruptedException
  {
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(keyPair, "keyPair");
    Objects.requireNonNull(tlsContexts, "tlsContexts");
    Objects.requireNonNull(configuration, "configuration");

    final var resources =
      CloseableCollection.create(() -> new NPAgentException(
        "One or more resources could not be closed.",
        new NPErrorCode("resources"),
        Map.of(),
        Optional.empty()
      ));

    return new NPAgentWorkerTaskMessaging(
      tlsContexts,
      keyPair,
      strings,
      resources,
      configuration
    );
  }

  private void runHandleMessage(
    final NPAMessageType message)
    throws InterruptedException, NPException, IOException
  {
    switch (message) {
      case final NPACommandType<?> c -> {
        this.runHandleCommand(c);
      }
      case final NPAEventType e -> {
        // Ignored
      }
      case final NPAResponseType r -> {
        // Ignored
      }
    }

    if (message instanceof final NPACommandS2CType<?> s2c) {
      this.runHandleS2CCommand(s2c);
      return;
    }
  }

  private void runHandleCommand(
    final NPACommandType<?> c)
    throws IOException, InterruptedException, NPException
  {
    switch (c) {
      case final NPACommandC2SType<?> c2s -> {
        // Ignored
      }
      case final NPACommandS2CType<?> s2c -> {
        this.runHandleS2CCommand(s2c);
      }
    }
  }

  private void runHandleS2CCommand(
    final NPACommandS2CType<?> s2c)
    throws InterruptedException, NPException, IOException
  {
    switch (s2c) {
      case final NPACommandSLatencyCheck c -> {
        this.runHandleCommandLatencyCheck(c);
      }
      case final NPACommandSWorkOffered offered -> {
        this.runHandleCommandWorkOffered(offered);
      }
      case final NPACommandSWorkSent sent -> {
        this.runHandleCommandWorkSent(sent);
      }
      case null, default -> throw new IllegalStateException();
    }
  }

  private void runHandleCommandWorkSent(
    final NPACommandSWorkSent sent)
    throws IOException, InterruptedException, NPException
  {
    LOG.debug("Sent work item {}.", sent.workItem());

    this.connection.send(
      new NPAResponseWorkSent(
        UUID.randomUUID(),
        sent.messageID(),
        sent.workItem().identifier(),
        false
      )
    );
  }

  private void runHandleCommandWorkOffered(
    final NPACommandSWorkOffered offered)
    throws IOException, InterruptedException, NPException
  {
    LOG.debug("Offered work item {}.", offered.workItem());

    this.connection.send(
      new NPAResponseWorkOffered(
        UUID.randomUUID(),
        offered.messageID(),
        offered.workItem(),
        false
      )
    );
  }

  private void runHandleCommandLatencyCheck(
    final NPACommandSLatencyCheck c)
    throws InterruptedException, NPException, IOException
  {
    LOG.debug("Responding to latency check.");
    this.connection.send(
      new NPAResponseLatencyCheck(
        UUID.randomUUID(),
        c.messageID(),
        c.timeCurrent(),
        OffsetDateTime.now()
      )
    );
  }

  private void runHandleMessages()
    throws InterruptedException, NPException, IOException
  {
    while (!this.connection.isClosed()) {
      final var messageOpt = this.connection.read();
      if (messageOpt.isPresent()) {
        this.runHandleMessage(messageOpt.get());
      } else {
        break;
      }
    }
  }

  @Override
  public void run()
  {
    LOG.debug("Start");

    while (!this.isClosed()) {
      try {
        this.connection =
          NPAgentConnection.open(
            this.strings,
            this.tlsContexts,
            this.keyPair,
            this.configuration
          );

        while (!this.isClosed()) {
          this.runHandleMessages();
        }
      } catch (final IOException | NPException e) {
        LOG.error("", e);
        pauseBriefly();
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      } finally {
        this.closeConnection();
      }
    }
  }

  private static void pauseBriefly()
  {
    try {
      Thread.sleep(1_000L);
    } catch (final InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  private void closeConnection()
  {
    try {
      final var c = this.connection;
      if (c != null) {
        c.close();
      }
    } catch (final IOException e) {
      LOG.error("", e);
    }
  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      LOG.debug("Close");
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String name()
  {
    return "com.io7m.northpike.agent.messaging";
  }
}
