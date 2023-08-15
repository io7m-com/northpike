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
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.io.IOException;
import java.net.Socket;
import java.time.Duration;
import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.ConcurrentLinkedQueue;

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

  private final NPAgentServerConnectionType connection;
  private final NPStrings strings;
  private final NPClockServiceType clock;
  private final NPDatabaseType database;
  private final NPEventServiceType events;
  private final NPTelemetryServiceType telemetry;
  private final ConcurrentLinkedQueue<InternalCommandType> enqueuedCommands;
  private final HashMap<String, String> attributes;
  private NPAgentID agentId;
  private NPAMessageType messageCurrent;

  private NPAgentTask(
    final NPAgentServerConnectionType inConnection,
    final NPStrings inStrings,
    final NPClockServiceType inClock,
    final NPDatabaseType inDatabase,
    final NPEventServiceType inEvents,
    final NPTelemetryServiceType inTelemetry)
  {
    this.connection =
      Objects.requireNonNull(inConnection, "connection");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.enqueuedCommands =
      new ConcurrentLinkedQueue<>();
    this.attributes =
      new HashMap<>();
  }

  /**
   * Create a new agent task for the given socket.
   *
   * @param services The service directory
   * @param socket   The socket
   *
   * @return A new agent task
   *
   * @throws NPServerException On errors
   * @throws IOException       On errors
   */

  public static NPAgentTask create(
    final RPServiceDirectoryType services,
    final Socket socket)
    throws NPException, IOException
  {
    final var strings =
      services.requireService(NPStrings.class);
    final var configuration =
      services.requireService(NPConfigurationServiceType.class);
    final var database =
      services.requireService(NPDatabaseType.class);
    final var events =
      services.requireService(NPEventServiceType.class);
    final var telemetry =
      services.requireService(NPTelemetryServiceType.class);
    final var clock =
      services.requireService(NPClockServiceType.class);

    final var sizeLimit =
      configuration.configuration()
        .agentConfiguration()
        .messageSizeLimit();

    try {
      return new NPAgentTask(
        NPAgentServerConnection.open(strings, sizeLimit, socket),
        strings,
        clock,
        database,
        events,
        telemetry
      );
    } catch (final NPException | IOException e) {
      try {
        socket.close();
      } catch (final IOException ex) {
        throw NPServerExceptions.errorIO(strings, ex);
      }
      throw e;
    }
  }

  @Override
  public void close()
    throws IOException
  {
    if (!this.isClosed()) {
      this.events.emit(
        new NPAgentDisconnected(
          this.connection.remoteAddress().getAddress(),
          this.connection.remoteAddress().getPort(),
          Optional.ofNullable(this.agentId)
        )
      );
      this.connection.close();
    }
  }

  @Override
  public void run()
  {
    try {
      MDC.put("Client", this.connection.remoteAddress().toString());

      while (!this.isClosed()) {
        final var receivedOpt = this.connection.read();
        if (receivedOpt.isPresent()) {
          final var received = receivedOpt.get();
          this.processReceivedMessageTimed(received);
        }

        while (!this.enqueuedCommands.isEmpty()) {
          this.processCommand(this.enqueuedCommands.poll());
        }
      }
    } catch (final Exception e) {
      LOG.debug("Fatal: ", e);
      this.closeQuietly();
    }
  }

  private void processCommand(
    final InternalCommandType command)
    throws InterruptedException, NPException, IOException
  {
    if (command instanceof InternalCommandType.LatencyCheck) {
      this.processCommandLatencyCheck();
      return;
    }

    throw new IllegalStateException(
      "Unrecognized command: %s".formatted(command.getClass())
    );
  }

  private void processCommandLatencyCheck()
    throws InterruptedException, NPException, IOException
  {
    LOG.debug("Latency: Performing check.");

    final var command =
      new NPACommandSLatencyCheck(
        UUID.randomUUID(),
        OffsetDateTime.now(this.clock.clock())
      );

    final var response =
      this.connection.ask(command);
    final var timeNow =
      OffsetDateTime.now(this.clock.clock());

    if (response instanceof final NPAResponseLatencyCheck latency) {
      final var duration =
        Duration.between(command.timeCurrent(), timeNow);

      LOG.debug("Latency: RTT {}", duration);
    }
  }

  private void closeQuietly()
  {
    try {
      this.close();
    } catch (final Exception ex) {
      LOG.debug("Close: ", ex);
    }
  }

  private void processReceivedMessageTimed(
    final NPAMessageType message)
    throws NPException, InterruptedException, IOException
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
    throws NPException, InterruptedException, IOException
  {
    this.attributes.clear();

    Optional.ofNullable(this.agentId)
      .ifPresent(agent -> {
        this.attributes.put(this.strings.format(AGENT_ID), agent.toString());
      });

    this.connection.send(
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
  }

  @Override
  public NPException fail(
    final NPStringConstantType errorMessage,
    final NPErrorCode errorCode)
  {
    final var exception =
      new NPServerException(
        this.strings.format(errorMessage),
        errorCode,
        this.attributes,
        Optional.empty()
      );

    try {
      this.connection.send(
        new NPAResponseError(
          UUID.randomUUID(),
          this.messageCurrent.messageID(),
          errorCode,
          this.strings.format(errorMessage),
          this.attributes
        )
      );
    } catch (final Exception e) {
      exception.addSuppressed(e);
    }
    return exception;
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
    return this.connection.isClosed();
  }

  /**
   * Schedule a latency check.
   */

  public void runLatencyCheck()
  {
    this.enqueuedCommands.add(InternalCommandType.LatencyCheck.LATENCY_CHECK);
  }

  private sealed interface InternalCommandType
  {
    /**
     * Run a latency check.
     */

    enum LatencyCheck implements InternalCommandType
    {
      LATENCY_CHECK
    }
  }
}
