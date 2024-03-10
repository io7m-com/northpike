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

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.api.NPAgentHostType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseConfiguration;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseFactoryType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.internal.console.NPAConsoleService;
import com.io7m.northpike.agent.internal.console.NPAConsoleServiceType;
import com.io7m.northpike.agent.internal.supervisor.NPAgentSupervisor;
import com.io7m.northpike.agent.internal.supervisor.NPAgentSupervisorType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventService;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tls.NPTLSContextService;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import io.opentelemetry.api.trace.SpanKind;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Clock;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;

/**
 * The basic agent host.
 */

public final class NPAgentHost implements NPAgentHostType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentHost.class);

  private final NPAgentHostConfiguration configuration;
  private final NPAgentDatabaseFactoryType databaseFactory;
  private final NPTelemetryServiceType telemetry;
  private final List<NPAWorkExecutorFactoryType> workExecutors;
  private final AtomicBoolean closed;
  private CloseableCollectionType<NPAgentException> resources;
  private NPStrings strings;
  private NPAgentDatabaseType database;

  private NPAgentHost(
    final NPAgentHostConfiguration inConfiguration,
    final NPAgentDatabaseFactoryType inDatabaseFactory,
    final NPTelemetryServiceType inTelemetry,
    final List<NPAWorkExecutorFactoryType> inWorkExecutors)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.databaseFactory =
      Objects.requireNonNull(inDatabaseFactory, "databaseFactory");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.workExecutors =
      Objects.requireNonNull(inWorkExecutors, "workExecutors");
    this.closed =
      new AtomicBoolean(true);
  }

  /**
   * Open the agent host.
   *
   * @param databases     The database factories
   * @param telemetries   The telemetry service factories
   * @param workExecutors The work executors
   * @param configuration The configuration
   *
   * @return An agent host
   *
   * @throws NPAgentException On errors
   */

  public static NPAgentHostType open(
    final List<NPAgentDatabaseFactoryType> databases,
    final List<NPTelemetryServiceFactoryType> telemetries,
    final List<NPAWorkExecutorFactoryType> workExecutors,
    final NPAgentHostConfiguration configuration)
    throws NPAgentException
  {
    Objects.requireNonNull(databases, "databases");
    Objects.requireNonNull(telemetries, "telemetries");
    Objects.requireNonNull(workExecutors, "workExecutors");
    Objects.requireNonNull(configuration, "configuration");

    final var telemetry =
      configuration.openTelemetry()
        .flatMap(c -> telemetries.stream().findFirst().map(f -> f.create(c)))
        .orElseGet(NPTelemetryNoOp::noop);

    final var dbConfiguration =
      configuration.database();

    final var databaseFactory =
      databases.stream()
        .filter(f -> Objects.equals(f.kind(), dbConfiguration.kind()))
        .findFirst()
        .orElseThrow(() -> errorNoUsableDatabase(dbConfiguration));

    return new NPAgentHost(
      configuration,
      databaseFactory,
      telemetry,
      workExecutors
    );
  }

  private static NPAgentException errorNoUsableDatabase(
    final NPAgentDatabaseConfiguration dbConfiguration)
  {
    throw new IllegalStateException();
  }

  @Override
  public void start()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(true, false)) {
      this.resources = NPAgentResources.createResources();

      final var startupSpan =
        this.telemetry.tracer()
          .spanBuilder("NPAgentHost.start")
          .setSpanKind(SpanKind.INTERNAL)
          .startSpan();

      try (var ignored = startupSpan.makeCurrent()) {
        this.startInSpan();
      } finally {
        startupSpan.end();
      }
    }
  }

  private void startInSpan()
    throws NPAgentException
  {
    try {
      this.strings =
        NPStrings.create(Locale.getDefault());
      this.database =
        this.resources.add(this.createDatabase(this.strings));
      final var services =
        this.resources.add(this.createServiceDirectory());

      final var console =
        services.requireService(NPAConsoleServiceType.class);

      console.start();
    } catch (final Exception e) {
      recordSpanException(e);

      try {
        this.close();
      } catch (final Exception ex) {
        e.addSuppressed(ex);
      }

      throw new NPAgentException(
        e.getMessage(),
        e,
        new NPErrorCode("startup"),
        Map.of(),
        Optional.empty()
      );
    }
  }

  private RPServiceDirectoryType createServiceDirectory()
    throws NPException
  {
    final var services = new RPServiceDirectory();
    services.register(NPStrings.class, this.strings);

    for (final var workExec : this.workExecutors) {
      services.register(NPAWorkExecutorFactoryType.class, workExec);
    }

    services.register(NPTelemetryServiceType.class, this.telemetry);
    services.register(NPAgentDatabaseType.class, this.database);
    services.register(
      NPEventServiceType.class,
      NPEventService.create(this.telemetry)
    );

    final var tls =
      NPTLSContextService.create(this.telemetry);
    services.register(NPTLSContextServiceType.class, tls);

    final var users =
      NPAConsoleService.create(services, this.configuration.console());
    services.register(NPAConsoleServiceType.class, users);

    final var supervisor =
      NPAgentSupervisor.create(services);
    services.register(NPAgentSupervisorType.class, supervisor);
    return services;
  }

  private NPAgentDatabaseType createDatabase(
    final NPStrings inStrings)
    throws NPAgentDatabaseException
  {
    return this.databaseFactory.open(
      new NPAgentDatabaseSetup(
        this.configuration.database(),
        this.telemetry,
        Clock.systemUTC(),
        inStrings
      ),
      status -> LOG.debug("Database: {}", status)
    );
  }

  @Override
  public void stop()
  {
    this.close();
  }

  @Override
  public void close()
  {
    if (this.closed.compareAndSet(false, true)) {
      // Nothing yet
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String toString()
  {
    return "[NPAgentHost 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
