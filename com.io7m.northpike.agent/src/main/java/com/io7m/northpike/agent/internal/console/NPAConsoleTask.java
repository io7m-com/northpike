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


package com.io7m.northpike.agent.internal.console;

import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.agent.api.NPAgentConsoleConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseConnectionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.internal.NPAgentExceptions;
import com.io7m.northpike.agent.internal.events.NPAgentEventType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.NPACResponseError;
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
import java.util.HashMap;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;
import static java.util.UUID.randomUUID;

/**
 * A task servicing a single connected client for the console service.
 */

public final class NPAConsoleTask implements Runnable,
  CloseableType, NPACCommandContextType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAConsoleTask.class);

  private final RPServiceDirectoryType services;
  private final NPAConsoleServerConnectionType connection;
  private final NPAgentConsoleConfiguration configuration;
  private final NPACCmd commandExecutor;
  private final NPStrings strings;
  private final NPAgentDatabaseType database;
  private final NPEventServiceType events;
  private final NPTelemetryServiceType telemetry;
  private final HashMap<String, String> attributes;
  private final HashMap<Class<?>, Object> properties;
  private final AtomicBoolean closed;
  private NPACMessageType messageCurrent;
  private volatile boolean authenticated;

  private NPAConsoleTask(
    final RPServiceDirectoryType inServices,
    final NPAConsoleServerConnectionType inConnection,
    final NPAgentConsoleConfiguration inConfiguration,
    final NPACCmd inCommandExecutor,
    final NPStrings inStrings,
    final NPAgentDatabaseType inDatabase,
    final NPEventServiceType inEvents,
    final NPTelemetryServiceType inTelemetry)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.connection =
      Objects.requireNonNull(inConnection, "open");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.commandExecutor =
      Objects.requireNonNull(inCommandExecutor, "commandExecutor");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.events =
      Objects.requireNonNull(inEvents, "events");
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
   * Create a new console task for the given socket.
   *
   * @param services      The service directory
   * @param configuration The console configuration
   * @param socket        The socket
   *
   * @return A new user task
   *
   * @throws NPException On errors
   * @throws IOException On errors
   */

  public static NPAConsoleTask create(
    final RPServiceDirectoryType services,
    final NPAgentConsoleConfiguration configuration,
    final Socket socket)
    throws NPException, IOException
  {
    Objects.requireNonNull(services, "services");
    Objects.requireNonNull(configuration, "configuration");
    Objects.requireNonNull(socket, "socket");

    final var strings =
      services.requireService(NPStrings.class);
    final var database =
      services.requireService(NPAgentDatabaseType.class);
    final var events =
      services.requireService(NPEventServiceType.class);
    final var telemetry =
      services.requireService(NPTelemetryServiceType.class);

    final var commandExecutor =
      NPACCmd.create();

    try {
      return new NPAConsoleTask(
        services,
        NPAConsoleServerConnection.open(strings, socket),
        configuration,
        commandExecutor,
        strings,
        database,
        events,
        telemetry
      );
    } catch (final NPException | IOException e) {
      try {
        socket.close();
      } catch (final IOException ex) {
        throw NPAgentExceptions.errorIO(strings, ex);
      }
      throw e;
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public void onAuthenticationRequire()
    throws NPException
  {
    if (!this.authenticated) {
      throw this.fail(ERROR_AUTHENTICATION, errorAuthentication());
    }
  }

  @Override
  public NPException fail(
    final NPStringConstantType message,
    final NPErrorCode errorCode)
  {
    final var exception =
      new NPAgentException(
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
      new NPAgentException(
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
      new NPAgentException(
        this.strings.format(message),
        errorCode,
        this.attributes,
        Optional.of(this.strings.format(suggestion))
      );

    return this.sendException(message, errorCode, exception);
  }

  private NPAgentException sendException(
    final NPStringConstantType message,
    final NPErrorCode errorCode,
    final NPAgentException exception)
  {
    try {
      this.connection.send(
        new NPACResponseError(
          randomUUID(),
          this.messageCurrent.messageID(),
          errorCode,
          this.strings.format(message),
          this.attributes
        )
      );
    } catch (final Exception e) {
      exception.addSuppressed(e);
    }

    LOG.debug("Fail: ", exception);
    return exception;
  }

  private void processReceivedMessageTimed(
    final NPACMessageType message)
    throws NPException, InterruptedException, IOException
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("ConsoleProcessMessage")
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
    final NPACMessageType message)
    throws NPException, InterruptedException, IOException
  {
    this.attributes.clear();
    this.connection.send(this.commandExecutor.execute(this, message));
  }

  @Override
  public void disconnect()
  {

  }

  @Override
  public NPAgentDatabaseConnectionType databaseConnection()
    throws NPException
  {
    return this.database.openConnection();
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
    this.attributes.put(this.strings.format(key), value);
  }

  @Override
  public void checkAccessKey(
    final String accessKey)
    throws NPException
  {
    if (!Objects.equals(this.configuration.accessKey(), accessKey)) {
      throw this.fail(ERROR_AUTHENTICATION, errorAuthentication());
    }
    this.authenticated = true;
  }

  @Override
  public void publishEvent(
    final NPAgentEventType e)
  {
    try {
      this.events.emit(e);
    } catch (final Exception ex) {
      LOG.warn("Failed to publish event: ", ex);
    }
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      try {
        // Nothing at the moment
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
}
