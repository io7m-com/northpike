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

package com.io7m.northpike.server.internal;

import com.io7m.idstore.model.IdName;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTelemetry;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryFactoryType;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.api.NPServerType;
import com.io7m.northpike.server.internal.agents.NPAgentServerSocketService;
import com.io7m.northpike.server.internal.agents.NPAgentServerSocketServiceType;
import com.io7m.northpike.server.internal.agents.NPAgentService;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.archives.NPArchiveService;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.assignments.NPAssignmentService;
import com.io7m.northpike.server.internal.assignments.NPAssignmentServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationService;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.idstore.NPIdstoreClients;
import com.io7m.northpike.server.internal.idstore.NPIdstoreClientsType;
import com.io7m.northpike.server.internal.maintenance.NPMaintenanceService;
import com.io7m.northpike.server.internal.metrics.NPMetricsService;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryService;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.server.internal.schedule.NPSchedulingService;
import com.io7m.northpike.server.internal.schedule.NPSchedulingServiceType;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUserServerSocketService;
import com.io7m.northpike.server.internal.users.NPUserServerSocketServiceType;
import com.io7m.northpike.server.internal.users.NPUserService;
import com.io7m.northpike.server.internal.users.NPUserServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventService;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceFactoryType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tls.NPTLSContextService;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.northpike.toolexec.api.NPTEvaluationService;
import com.io7m.northpike.toolexec.api.NPTEvaluationServiceType;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.StatusCode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Clock;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.ServiceLoader;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;
import static java.lang.Integer.toUnsignedString;

/**
 * The basic server frontend.
 */

public final class NPServer implements NPServerType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPServer.class);

  private final NPServerConfiguration configuration;
  private final AtomicBoolean running;
  private CloseableCollectionType<NPServerException> resources;
  private NPTelemetryServiceType telemetry;
  private NPDatabaseType database;

  /**
   * The basic server frontend.
   *
   * @param inConfiguration The server configuration
   */

  public NPServer(
    final NPServerConfiguration inConfiguration)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.resources =
      NPServerResources.createResources();
    this.running =
      new AtomicBoolean(false);
  }

  @Override
  public void start()
    throws NPServerException
  {
    try {
      if (this.running.compareAndSet(false, true)) {
        this.resources = NPServerResources.createResources();
        this.telemetry = this.createTelemetry();

        final var startupSpan =
          this.telemetry.tracer()
            .spanBuilder("NPServer.start")
            .setSpanKind(SpanKind.INTERNAL)
            .startSpan();

        try (var ignored = startupSpan.makeCurrent()) {
          this.startInSpan();
        } finally {
          startupSpan.end();
        }
      }
    } catch (final Throwable e) {
      this.close();
      throw e;
    }
  }

  private void startInSpan()
    throws NPServerException
  {
    try {
      final var dbTelemetry =
        new NPDatabaseTelemetry(
          this.telemetry.isNoOp(),
          this.telemetry.meter(),
          this.telemetry.tracer()
        );

      this.database =
        this.resources.add(this.createDatabase(dbTelemetry));
      final var services =
        this.resources.add(this.createServiceDirectory(this.database));

      final var users =
        services.requireService(NPUserServiceType.class);
      final var agents =
        services.requireService(NPAgentServiceType.class);
      final var repository =
        services.requireService(NPRepositoryServiceType.class);
      final var archive =
        services.requireService(NPArchiveServiceType.class);

      final var all =
        CompletableFuture.allOf(
          agents.start(),
          archive.start(),
          repository.start(),
          users.start()
        );

      all.get(60L, TimeUnit.SECONDS);

      /*
       * After everything is started, load the security policy. The default
       * policy is deny-all, so this effectively opens the server for access.
       */

      NPSecurity.setPolicy(NPSecurityPolicy.open());
    } catch (final NPDatabaseException e) {
      recordSpanException(e);

      try {
        this.close();
      } catch (final NPServerException ex) {
        e.addSuppressed(ex);
      }

      throw new NPServerException(
        e.getMessage(),
        e,
        new NPErrorCode("database"),
        Map.of(),
        Optional.empty()
      );

    } catch (final Exception e) {
      recordSpanException(e);

      try {
        this.close();
      } catch (final NPServerException ex) {
        e.addSuppressed(ex);
      }

      throw new NPServerException(
        e.getMessage(),
        e,
        new NPErrorCode("startup"),
        Map.of(),
        Optional.empty()
      );
    }
  }

  private RPServiceDirectoryType createServiceDirectory(
    final NPDatabaseType newDatabase)
    throws NPServerException
  {
    final var services = new RPServiceDirectory();
    final var strings = this.configuration.strings();
    services.register(NPStrings.class, strings);

    services.register(NPTelemetryServiceType.class, this.telemetry);
    services.register(NPDatabaseType.class, newDatabase);

    for (final var reposFactory : ServiceLoader.load(NPSCMRepositoryFactoryType.class)) {
      services.register(NPSCMRepositoryFactoryType.class, reposFactory);
    }

    for (final var toolFactory : ServiceLoader.load(NPToolFactoryType.class)) {
      services.register(NPToolFactoryType.class, toolFactory);
    }

    final var metrics = new NPMetricsService(this.telemetry);
    services.register(NPMetricsServiceType.class, metrics);

    final var events = NPEventService.create(this.telemetry);
    services.register(NPEventServiceType.class, events);

    final var clock = new NPClock(Clock.systemUTC());
    services.register(NPClockServiceType.class, clock);

    final var config =
      NPConfigurationService.create(this.configuration);
    services.register(NPConfigurationServiceType.class, config);

    final var tls = NPTLSContextService.create(this.telemetry);
    services.register(NPTLSContextServiceType.class, tls);

    services.register(
      NPTEvaluationServiceType.class,
      NPTEvaluationService.createFromServiceLoader(strings)
    );

    final var archive = NPArchiveService.create(services);
    services.register(NPArchiveServiceType.class, archive);

    final var repository = NPRepositoryService.create(services);
    services.register(NPRepositoryServiceType.class, repository);

    final var maintenance =
      NPMaintenanceService.create(
        clock,
        this.telemetry,
        config,
        archive,
        tls,
        this.database
      );
    services.register(NPMaintenanceService.class, maintenance);

    final var agentSockets =
      NPAgentServerSocketService.create(
        strings,
        tls,
        this.configuration.agentConfiguration()
      );
    services.register(NPAgentServerSocketServiceType.class, agentSockets);

    final var agents = NPAgentService.create(services);
    services.register(NPAgentServiceType.class, agents);

    final var userSockets =
      NPUserServerSocketService.create(
        strings,
        tls,
        this.configuration.userConfiguration()
      );
    services.register(NPUserServerSocketServiceType.class, userSockets);

    final var idstoreClients =
      NPIdstoreClients.create(
        this.configuration.locale(),
        this.telemetry,
        this.configuration.idstoreConfiguration()
      );
    services.register(NPIdstoreClientsType.class, idstoreClients);

    final var assignmentService =
      NPAssignmentService.create(services);
    services.register(NPAssignmentServiceType.class, assignmentService);

    final var schedulingService =
      NPSchedulingService.create(
        clock,
        this.telemetry,
        config,
        events,
        this.database,
        repository,
        assignmentService
      );
    services.register(NPSchedulingServiceType.class, schedulingService);

    final var users = NPUserService.create(services);
    services.register(NPUserServiceType.class, users);
    return services;
  }

  private NPDatabaseType createDatabase(
    final NPDatabaseTelemetry dbTelemetry)
    throws NPDatabaseException
  {
    return this.configuration.databases()
      .open(
        this.configuration.databaseConfiguration(),
        dbTelemetry,
        event -> {

        });
  }

  private NPTelemetryServiceType createTelemetry()
  {
    return this.configuration.openTelemetry()
      .flatMap(config -> {
        final var loader =
          ServiceLoader.load(NPTelemetryServiceFactoryType.class);
        return loader.findFirst().map(f -> f.create(config));
      }).orElseGet(NPTelemetryNoOp::noop);
  }

  @Override
  public NPDatabaseType database()
  {
    if (!this.running.get()) {
      throw new IllegalStateException("Server is not started.");
    }

    return this.database;
  }

  @Override
  public NPServerConfiguration configuration()
  {
    return this.configuration;
  }

  @Override
  public boolean isClosed()
  {
    return !this.running.get();
  }

  @Override
  public void setUserAsAdmin(
    final UUID adminId,
    final IdName adminName)
    throws NPServerException
  {
    Objects.requireNonNull(adminId, "adminId");
    Objects.requireNonNull(adminName, "adminName");

    final var newTelemetry =
      this.createTelemetry();

    final var dbTelemetry =
      new NPDatabaseTelemetry(
        newTelemetry.isNoOp(),
        newTelemetry.meter(),
        newTelemetry.tracer()
      );

    final var dbConfiguration =
      this.configuration.databaseConfiguration()
        .withoutUpgradeOrCreate();

    try (var newDatabase =
           this.configuration.databases()
             .open(dbConfiguration, dbTelemetry, event -> {

             })) {

      final var span =
        newTelemetry.tracer()
          .spanBuilder("SetUserAsAdmin")
          .startSpan();

      try (var ignored = span.makeCurrent()) {
        setUserAsAdminSpan(newDatabase, adminId, adminName);
      } catch (final Exception e) {
        span.recordException(e);
        span.setStatus(StatusCode.ERROR);
        throw e;
      } finally {
        span.end();
      }
    } catch (final NPDatabaseException e) {
      throw new NPServerException(
        e.getMessage(),
        e,
        e.errorCode(),
        e.attributes(),
        e.remediatingAction()
      );
    }
  }

  private static void setUserAsAdminSpan(
    final NPDatabaseType database,
    final UUID adminId,
    final IdName adminName)
    throws NPServerException
  {
    try (var connection =
           database.openConnection(NORTHPIKE)) {
      try (var transaction =
             connection.openTransaction()) {
        final var put =
          transaction.queries(NPDatabaseQueriesUsersType.PutType.class);

        transaction.setOwner(new NPAuditUserOrAgentType.User(adminId));
        put.execute(
          new NPUser(
            adminId,
            adminName,
            new MSubject(
              NPSecRole.allRoles()
                .stream().map(NPSecRole::role)
                .collect(Collectors.toUnmodifiableSet())
            )
          )
        );

        transaction.commit();
      }
    } catch (final NPDatabaseException e) {
      throw new NPServerException(
        e.getMessage(),
        e,
        e.errorCode(),
        e.attributes(),
        e.remediatingAction()
      );
    }
  }

  @Override
  public void close()
    throws NPServerException
  {
    if (this.running.compareAndSet(true, false)) {
      LOG.debug("Shutting down server.");
      this.resources.close();
    }
  }

  @Override
  public String toString()
  {
    return "[NPServer 0x%s]".formatted(toUnsignedString(this.hashCode(), 16));
  }
}
