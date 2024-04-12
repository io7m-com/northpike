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


package com.io7m.northpike.server.internal.users;

import com.io7m.idstore.user_client.api.IdUClientException;
import com.io7m.idstore.user_client.api.IdUClientType;
import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPUserConnected;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.idstore.NPIdstoreClientsType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.io.IOException;
import java.net.Socket;
import java.net.URI;
import java.nio.channels.ClosedChannelException;
import java.util.HashMap;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_ID;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;
import static java.util.UUID.randomUUID;

/**
 * A task for a single connected user.
 */

public final class NPUserTask
  implements Runnable, CloseableType, NPUserCommandContextType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPUserTask.class);

  private final RPServiceDirectoryType services;
  private final NPUserServerConnectionType connection;
  private final NPUCmd commandExecutor;
  private final NPConfigurationServiceType configuration;
  private final NPStrings strings;
  private final NPClockServiceType clock;
  private final NPDatabaseType database;
  private final NPEventServiceType events;
  private final NPIdstoreClientsType idstore;
  private final NPTelemetryServiceType telemetry;
  private final HashMap<String, String> attributes;
  private final HashMap<Class<?>, Object> properties;
  private final AtomicBoolean closed;
  private UUID userId;
  private NPUMessageType messageCurrent;

  private NPUserTask(
    final RPServiceDirectoryType inServices,
    final NPUserServerConnectionType inConnection,
    final NPUCmd inCommandExecutor,
    final NPConfigurationServiceType inConfiguration,
    final NPStrings inStrings,
    final NPClockServiceType inClock,
    final NPDatabaseType inDatabase,
    final NPEventServiceType inEvents,
    final NPIdstoreClientsType inIdstore,
    final NPTelemetryServiceType inTelemetry)
  {
    this.services =
      Objects.requireNonNull(inServices, "inServices");
    this.connection =
      Objects.requireNonNull(inConnection, "connection");
    this.commandExecutor =
      Objects.requireNonNull(inCommandExecutor, "commandExecutor");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.idstore =
      Objects.requireNonNull(inIdstore, "idstore");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.attributes =
      new HashMap<>();
    this.properties =
      new HashMap<>();
    this.closed =
      new AtomicBoolean(false);
  }

  /**
   * Create a new user task for the given socket.
   *
   * @param services The service directory
   * @param socket   The socket
   *
   * @return A new user task
   *
   * @throws NPServerException On errors
   * @throws IOException       On errors
   */

  public static NPUserTask create(
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
    final var idstore =
      services.requireService(NPIdstoreClientsType.class);

    final var commandExecutor =
      NPUCmd.create();

    final var sizeLimit =
      configuration.configuration()
        .userConfiguration()
        .messageSizeLimit();

    try {
      return new NPUserTask(
        services,
        NPUserServerConnection.open(strings, sizeLimit, socket),
        commandExecutor,
        configuration,
        strings,
        clock,
        database,
        events,
        idstore,
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
    if (this.closed.compareAndSet(false, true)) {
      try {
        this.events.emit(
          new NPUserDisconnected(
            this.connection.remoteAddress().getAddress(),
            this.connection.remoteAddress().getPort(),
            Optional.ofNullable(this.userId)
          )
        );
      } finally {
        this.connection.close();
      }
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
      }
    } catch (final ClosedChannelException e) {
      this.closeQuietly();
    } catch (final Exception e) {
      LOG.debug("Fatal: ", e);
      this.closeQuietly();
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
    final NPUMessageType message)
    throws NPException, InterruptedException, IOException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("UserProcessMessage")
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
    final NPUMessageType message)
    throws NPException, InterruptedException, IOException
  {
    this.attributes.clear();

    Optional.ofNullable(this.userId)
      .ifPresent(user -> {
        this.attributes.put(this.strings.format(AGENT_ID), user.toString());
      });

    this.connection.send(this.commandExecutor.execute(this, message));
  }

  @Override
  public String toString()
  {
    return "[NPUserTask 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }


  @Override
  public boolean isClosed()
  {
    return this.connection.isClosed();
  }

  /**
   * @return The user ID for this task
   */

  public UUID userId()
  {
    return this.userId;
  }

  @Override
  public IdUClientType createIdstoreClient()
    throws IdUClientException, InterruptedException
  {
    return this.idstore.createClient();
  }

  @Override
  public NPUser onAuthenticationRequire()
    throws NPException
  {
    final var id = this.userId;
    if (id == null) {
      throw this.fail(ERROR_AUTHENTICATION, errorAuthentication());
    }

    try (var c = this.databaseConnection()) {
      try (var transaction = c.openTransaction()) {
        return transaction.queries(NPDatabaseQueriesUsersType.GetType.class)
          .execute(id)
          .orElseThrow(() -> {
            return this.fail(ERROR_AUTHENTICATION, errorAuthentication());
          });
      }
    }
  }

  @Override
  public void onAuthenticationComplete(
    final UUID user)
  {
    this.userId = Objects.requireNonNull(user, "user");
    this.events.emit(
      new NPUserAuthenticated(
        this.connection.remoteAddress().getAddress(),
        this.connection.remoteAddress().getPort(),
        this.userId
      )
    );
  }

  @Override
  public NPException fail(
    final NPStringConstantType message,
    final NPErrorCode errorCode)
  {
    final var exception =
      new NPServerException(
        this.strings.format(message),
        errorCode,
        this.attributes,
        Optional.empty()
      );

    return this.sendException(message, errorCode, exception);
  }

  @Override
  public NPException fail(
    final Exception cause,
    final NPStringConstantType message,
    final NPErrorCode errorCode)
  {
    final var exception =
      new NPServerException(
        this.strings.format(message),
        cause,
        errorCode,
        this.attributes,
        Optional.empty()
      );

    return this.sendException(message, errorCode, exception);
  }

  @Override
  public NPException failWithRemediation(
    final NPStringConstants message,
    final NPErrorCode errorCode,
    final NPStringConstants suggestion)
  {
    final var exception =
      new NPServerException(
        this.strings.format(message),
        errorCode,
        this.attributes,
        Optional.of(this.strings.format(suggestion))
      );

    return this.sendException(message, errorCode, exception);
  }

  private NPServerException sendException(
    final NPStringConstantType message,
    final NPErrorCode errorCode,
    final NPServerException exception)
  {
    try {
      this.connection.send(
        new NPUResponseError(
          randomUUID(),
          this.messageCurrent.messageID(),
          errorCode,
          this.strings.format(message),
          this.attributes,
          exception.remediatingAction()
        )
      );
    } catch (final Exception e) {
      exception.addSuppressed(e);
    }

    LOG.debug("Fail: ", exception);
    return exception;
  }

  @Override
  public void disconnect()
  {

  }

  @Override
  public NPDatabaseConnectionType databaseConnection()
    throws NPException
  {
    return this.database.openConnection(NORTHPIKE);
  }

  @Override
  public URI idstoreLoginURI()
  {
    return this.configuration.configuration()
      .idstoreConfiguration()
      .baseURI();
  }

  @Override
  public <T> void setProperty(
    final Class<T> key,
    final T value)
  {
    this.properties.put(
      Objects.requireNonNull(key, "key"),
      Objects.requireNonNull(value, "value")
    );
  }

  @Override
  public <T> Optional<T> property(
    final Class<T> key)
  {
    Objects.requireNonNull(key, "key");
    return Optional.ofNullable((T) this.properties.get(key));
  }

  @Override
  public RPServiceDirectoryType services()
  {
    return this.services;
  }

  @Override
  public void setAttribute(
    final NPStringConstantType key,
    final String value)
  {
    this.attributes.put(
      this.strings.format(key),
      value
    );
  }

  /**
   * @return The currently connected/authenticated user (if any)
   */

  public Optional<NPUserConnected> user()
  {
    final var uid = this.userId;
    if (uid != null) {
      try {
        try (var connection = this.databaseConnection()) {
          try (var transaction = connection.openTransaction()) {
            return transaction.queries(NPDatabaseQueriesUsersType.GetType.class)
              .execute(uid)
              .map(u -> new NPUserConnected(
                u.userId(),
                u.name(),
                this.connection.remoteAddress()
              ));
          }
        }
      } catch (final NPException e) {
        recordSpanException(e);
      }
    }
    return Optional.empty();
  }
}
