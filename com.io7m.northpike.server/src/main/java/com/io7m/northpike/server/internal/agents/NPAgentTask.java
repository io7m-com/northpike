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


package com.io7m.northpike.server.internal.agents;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.net.Socket;
import java.time.Duration;
import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_ID;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;

/**
 * A task for a single connected agent.
 */

public final class NPAgentTask
  implements Runnable, CloseableType, NPAgentCommandContextType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentTask.class);

  private final NPStrings strings;
  private final NPTelemetryServiceType telemetry;
  private final NPClockServiceType clock;
  private final AtomicBoolean closed;
  private final NPAgentServerConnectionType connection;
  private final CloseableCollectionType<NPServerException> resources;
  private final ScheduledExecutorService periodics;
  private final HashMap<String, String> attributes;
  private final NPDatabaseType database;
  private final NPEventServiceType events;
  private NPAgentID agentId;
  private NPAMessageType messageCurrent;

  NPAgentTask(
    final NPStrings inStrings,
    final NPTelemetryServiceType inTelemetry,
    final NPClockServiceType inClock,
    final NPDatabaseType inDatabase,
    final NPEventServiceType inEvents,
    final NPServerAgentConfiguration agentConfiguration,
    final Socket inSocket)
    throws Exception
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.database =
      Objects.requireNonNull(inDatabase, "access");
    this.events =
      Objects.requireNonNull(inEvents, "events");

    this.resources = NPServerResources.createResources();

    try {
      this.attributes = new HashMap<>();
      this.closed = new AtomicBoolean(false);
      this.resources.add(inSocket);
      this.periodics = createPeriodicExecutor();
      this.resources.add(this.periodics::shutdown);
      this.connection =
        this.resources.add(
          new NPAgentServerConnection(this.strings, agentConfiguration, inSocket)
        );
    } catch (final Exception e) {
      this.resources.close();
      throw e;
    }
  }

  private static ScheduledExecutorService createPeriodicExecutor()
  {
    return Executors.newSingleThreadScheduledExecutor(runnable -> {
      final var thread = new Thread(runnable);
      thread.setName(
        "com.io7m.northpike.agent.periodic[%d]"
          .formatted(Long.valueOf(thread.getId()))
      );
      thread.setDaemon(true);
      return thread;
    });
  }

  @Override
  public void close()
    throws NPException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.events.emit(
        new NPAgentDisconnected(
          this.connection.remoteAddress().getAddress(),
          this.connection.remoteAddress().getPort(),
          Optional.ofNullable(this.agentId)
        )
      );

      LOG.debug("Close: {}", this);
      this.resources.close();
    }
  }

  @Override
  public void run()
  {
    try {
      MDC.put("Client", this.connection.remoteAddress().toString());

      while (!this.closed.get()) {
        final var received =
          this.connection.takeReceivedMessages();

        for (final var message : received) {
          this.processReceivedMessageTimed(message);
        }
      }
    } catch (final NPException e) {
      LOG.debug("Fatal: ", e);
      this.closeQuietly();
    }
  }

  private void doLatencyCheck()
  {
    LOG.debug("Latency: Performing check.");

    try {
      final var timeSent =
        OffsetDateTime.now(this.clock.clock());

      final var future =
        this.connection.submitExpectingResponse(
          new NPACommandSLatencyCheck(UUID.randomUUID(), timeSent)
        );

      future.thenAccept(response -> {
        final var timeNow =
          OffsetDateTime.now(this.clock.clock());

        if (response instanceof final NPAResponseLatencyCheck latency) {
          final var duration =
            Duration.between(timeSent, timeNow);

          LOG.debug("Latency: RTT {}", duration);
        }
      });
    } catch (final Exception e) {
      LOG.debug("Latency: ", e);
    }
  }

  private void closeQuietly()
  {
    try {
      this.close();
    } catch (final NPException ex) {
      LOG.debug("Close: ", ex);
    }
  }

  private void processReceivedMessageTimed(
    final NPAMessageType message)
    throws NPException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("AgentProcessMessage")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      span.setAttribute("Message", message.getClass().getSimpleName());
      span.setAttribute("MessageID", message.messageID().toString());
      this.messageCurrent = message;
      this.processReceivedMessage(message);
    } catch (final Exception e) {
      recordSpanException(e);
      throw e;
    } finally {
      span.end();
    }
  }

  private void processReceivedMessage(
    final NPAMessageType message)
    throws NPException
  {
    this.attributes.clear();

    Optional.ofNullable(this.agentId)
      .ifPresent(agent -> {
        this.attributes.put(this.strings.format(AGENT_ID), agent.toString());
      });

    this.connection.submitExpectingNoResponse(
      new NPACmd().execute(this, message)
    );
  }

  @Override
  public String toString()
  {
    return "[NPAgentTask 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public NPAgentID authenticationRequire()
    throws NPException
  {
    final var id = this.agentId;
    if (id == null) {
      throw this.fail(ERROR_AUTHENTICATION, errorAuthentication());
    }
    return id;
  }

  @Override
  public void authenticationComplete(
    final NPAgentDescription agent)
  {
    this.agentId = agent.id();

    this.events.emit(
      new NPAgentAuthenticated(
        this.connection.remoteAddress().getAddress(),
        this.connection.remoteAddress().getPort(),
        this.agentId
      )
    );

    this.periodics.scheduleAtFixedRate(
      this::doLatencyCheck,
      100L,
      1000L,
      TimeUnit.MILLISECONDS
    );
  }

  @Override
  public NPException fail(
    final NPStringConstantType errorMessage,
    final NPErrorCode errorCode)
  {
    this.connection.submitExpectingNoResponse(
      new NPAResponseError(
        UUID.randomUUID(),
        this.messageCurrent.messageID(),
        errorCode,
        this.strings.format(errorMessage),
        this.attributes
      )
    );

    return new NPServerException(
      this.strings.format(errorMessage),
      errorCode,
      this.attributes,
      Optional.empty()
    );
  }

  @Override
  public void disconnect()
  {
    this.closeQuietly();
  }

  @Override
  public Optional<NPAgentDescription> agentFindForId(
    final NPAgentID id)
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        final var get =
          transaction.queries(NPDatabaseQueriesAgentsType.GetType.class);
        return get.execute(id);
      }
    }
  }

  @Override
  public Optional<NPAgentDescription> agentFindForKey(
    final NPKey key)
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        final var get =
          transaction.queries(NPDatabaseQueriesAgentsType.GetByKeyType.class);
        return get.execute(key);
      }
    }
  }

  @Override
  public void agentUpdate(
    final NPAgentDescription agent)
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        final var put =
          transaction.queries(NPDatabaseQueriesAgentsType.PutType.class);
        put.execute(agent);
        transaction.commit();
      }
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
