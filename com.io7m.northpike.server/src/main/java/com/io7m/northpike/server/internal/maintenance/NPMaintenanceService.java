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


package com.io7m.northpike.server.internal.maintenance;


import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredArchivesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredAssignmentExecutionsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredLoginChallengesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.UpdateUserRolesType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.repetoir.core.RPServiceType;
import io.opentelemetry.api.trace.SpanKind;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.time.Duration;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;

/**
 * A service that performs nightly database maintenance.
 */

public final class NPMaintenanceService
  implements RPServiceType, AutoCloseable
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPMaintenanceService.class);

  private final ExecutorService executor;
  private final NPClockServiceType clock;
  private final NPTelemetryServiceType telemetry;
  private final NPDatabaseType database;
  private final NPTLSContextServiceType tlsContexts;
  private final NPArchiveServiceType archives;
  private final NPConfigurationServiceType configuration;
  private final AtomicBoolean closed;
  private final CompletableFuture<Void> waitTLS;
  private final CompletableFuture<Void> waitMaintenance;

  private NPMaintenanceService(
    final ExecutorService inExecutor,
    final NPClockServiceType inClock,
    final NPTelemetryServiceType inTelemetry,
    final NPDatabaseType inDatabase,
    final NPTLSContextServiceType inTlsContexts,
    final NPArchiveServiceType inArchives,
    final NPConfigurationServiceType inConfiguration)
  {
    this.executor =
      Objects.requireNonNull(inExecutor, "executor");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.tlsContexts =
      Objects.requireNonNull(inTlsContexts, "tlsContexts");
    this.archives =
      Objects.requireNonNull(inArchives, "archives");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.closed =
      new AtomicBoolean(false);
    this.waitTLS =
      new CompletableFuture<Void>();
    this.waitMaintenance =
      new CompletableFuture<Void>();
  }

  /**
   * A service that performs nightly maintenance.
   *
   * @param archives      The archive service
   * @param clock         The clock
   * @param telemetry     The telemetry service
   * @param database      The database
   * @param configuration The configuration service
   * @param tlsContexts   The TLS contexts
   *
   * @return The service
   */

  public static NPMaintenanceService create(
    final NPClockServiceType clock,
    final NPTelemetryServiceType telemetry,
    final NPConfigurationServiceType configuration,
    final NPArchiveServiceType archives,
    final NPTLSContextServiceType tlsContexts,
    final NPDatabaseType database)
  {
    Objects.requireNonNull(archives, "archives");
    Objects.requireNonNull(clock, "clock");
    Objects.requireNonNull(configuration, "configuration");
    Objects.requireNonNull(database, "database");
    Objects.requireNonNull(telemetry, "telemetry");
    Objects.requireNonNull(tlsContexts, "tlsContexts");

    final var executor =
      Executors.newThreadPerTaskExecutor(
        Thread.ofVirtual()
          .name("com.io7m.northpike.maintenance-", 0L)
          .factory()
      );

    final var maintenanceService =
      new NPMaintenanceService(
        executor,
        clock,
        telemetry,
        database,
        tlsContexts,
        archives,
        configuration
      );

    executor.execute(maintenanceService::runTLSReloadTask);
    executor.execute(maintenanceService::runMaintenanceTask);
    return maintenanceService;
  }

  /**
   * A task that executes maintenance once when the service starts, and then
   * again at every subsequent midnight.
   */

  private void runMaintenanceTask()
  {
    while (!this.closed.get()) {
      try {
        this.runMaintenance();
      } catch (final Exception e) {
        // Not important.
      }

      final var timeNow =
        this.clock.now();
      final var timeNextMidnight =
        timeNow.withHour(0)
          .withMinute(0)
          .withSecond(0)
          .plusDays(1L);

      final var untilNext =
        Duration.between(timeNow, timeNextMidnight);

      try {
        this.waitMaintenance.get(untilNext.toSeconds(), TimeUnit.SECONDS);
      } catch (final Exception e) {
        break;
      }
    }
  }

  /**
   * A task that reloads TLS contexts at the specified reload interval.
   */

  private void runTLSReloadTask()
  {
    final var reloadIntervalOpt =
      this.configuration.configuration()
        .maintenanceConfiguration()
        .tlsReloadInterval();

    if (reloadIntervalOpt.isEmpty()) {
      return;
    }

    final var reloadInterval =
      reloadIntervalOpt.get();

    while (!this.closed.get()) {
      try {
        this.runTLSReload();
      } catch (final Exception e) {
        // Not important.
      }

      try {
        this.waitTLS.get(reloadInterval.toSeconds(), TimeUnit.SECONDS);
      } catch (final Exception e) {
        break;
      }
    }
  }

  private void runTLSReload()
  {
    LOG.info("Reloading TLS contexts");
    this.tlsContexts.reload();
  }

  private void runMaintenance()
  {
    LOG.info("Maintenance task starting");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("Maintenance")
        .setSpanKind(SpanKind.INTERNAL)
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      try (var connection =
             this.database.openConnection(NPDatabaseRole.NORTHPIKE)) {
        try (var transaction =
               connection.openTransaction()) {

          transaction.setOwner(new NPAuditOwnerType.Server());

          try {
            updateUserRoles(transaction);
          } catch (final Exception e) {
            span.recordException(e);
          }

          try {
            this.deleteExpiredArchives(transaction);
          } catch (final Exception e) {
            span.recordException(e);
          }

          try {
            this.deleteExpiredAssignmentExecutions(transaction);
          } catch (final Exception e) {
            span.recordException(e);
          }

          try {
            this.deleteExpiredLoginChallenges(transaction);
          } catch (final Exception e) {
            span.recordException(e);
          }

          LOG.info("Maintenance task completed.");
        }
      }
    } catch (final Exception e) {
      LOG.error("Maintenance task failed: ", e);
      span.recordException(e);
    } finally {
      span.end();
    }
  }

  private void deleteExpiredLoginChallenges(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException
  {
    final var maximumAge =
      this.configuration.configuration()
        .maintenanceConfiguration()
        .agentLoginChallengesMaximumAge();

    final var cutoffTime =
      this.clock.now()
        .minusSeconds(maximumAge.toSeconds());

    final var deleted =
      transaction.queries(DeleteExpiredLoginChallengesType.class)
        .execute(cutoffTime);

    transaction.commit();
    LOG.debug("Deleted {} old agent login challenge records.", deleted);
  }

  private void deleteExpiredAssignmentExecutions(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException
  {
    final var maximumAge =
      this.configuration.configuration()
        .maintenanceConfiguration()
        .assignmentExecutionsMaximumAge();

    final var cutoffTime =
      this.clock.now()
        .minusSeconds(maximumAge.toSeconds());

    final var deleted =
      transaction.queries(DeleteExpiredAssignmentExecutionsType.class)
        .execute(cutoffTime);

    transaction.commit();
    LOG.debug("Deleted {} old assignment execution records.", deleted);
  }

  private void deleteExpiredArchives(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException, IOException
  {
    final var maximumAge =
      this.configuration.configuration()
        .maintenanceConfiguration()
        .archivesMaximumAge();

    final var cutoffTime =
      this.clock.now()
        .minusSeconds(maximumAge.toSeconds());

    final var tokens =
      transaction.queries(DeleteExpiredArchivesType.class)
        .execute(cutoffTime);

    for (final var token : tokens) {
      this.archives.deleteArchive(token);
    }

    transaction.commit();
  }

  private static void updateUserRoles(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException
  {
    transaction.queries(UpdateUserRolesType.class).execute(UNIT);
    transaction.commit();
  }

  @Override
  public String description()
  {
    return "Server maintenance service.";
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.waitTLS.complete(null);
      this.waitMaintenance.complete(null);
      this.executor.close();
    }
  }

  @Override
  public String toString()
  {
    return "[NPMaintenanceService 0x%s]"
      .formatted(Long.toUnsignedString(this.hashCode(), 16));
  }
}
