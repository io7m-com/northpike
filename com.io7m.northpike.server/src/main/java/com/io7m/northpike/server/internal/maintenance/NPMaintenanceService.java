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


import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredArchivesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.UpdateUserRolesType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.tls.NPTLSContextServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceType;
import io.opentelemetry.api.trace.SpanKind;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.time.Duration;
import java.time.temporal.ChronoUnit;
import java.util.Objects;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;

/**
 * A service that performs nightly database maintenance.
 */

public final class NPMaintenanceService
  implements RPServiceType, AutoCloseable
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPMaintenanceService.class);

  private final ScheduledExecutorService executor;
  private final NPClockServiceType clock;
  private final NPTelemetryServiceType telemetry;
  private final NPDatabaseType database;
  private final NPTLSContextServiceType tlsContexts;
  private final NPArchiveServiceType archives;
  private final NPConfigurationServiceType configuration;

  private NPMaintenanceService(
    final ScheduledExecutorService inExecutor,
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
      Executors.newSingleThreadScheduledExecutor(r -> {
        final var thread = new Thread(r);
        thread.setDaemon(true);
        thread.setName(
          "com.io7m.northpike.server.internal.maintenance.NPMaintenanceService[%d]"
            .formatted(thread.getId())
        );
        return thread;
      });

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

    final var timeNow =
      clock.now();
    final var timeNextMidnight =
      timeNow.withHour(0)
        .withMinute(0)
        .withSecond(0)
        .plusDays(1L);

    final var initialDelay =
      Duration.between(timeNow, timeNextMidnight).toSeconds();

    final var period =
      Duration.of(1L, ChronoUnit.DAYS)
        .toSeconds();

    /*
     * Start TLS context reloading if needed.
     */

    configuration.configuration()
      .maintenanceConfiguration()
      .tlsReloadInterval()
      .ifPresent(duration -> {
        executor.scheduleAtFixedRate(
          maintenanceService::runTLSReload,
          duration.toSeconds(),
          duration.toSeconds(),
          TimeUnit.SECONDS
        );
      });

    /*
     * Run maintenance as soon as the service starts.
     */

    executor.submit(maintenanceService::runMaintenance);

    /*
     * Schedule maintenance to run at each midnight.
     */

    executor.scheduleAtFixedRate(
      maintenanceService::runMaintenance,
      initialDelay,
      period,
      TimeUnit.SECONDS
    );

    return maintenanceService;
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
    this.executor.shutdown();
  }

  @Override
  public String toString()
  {
    return "[NPMaintenanceService 0x%s]"
      .formatted(Long.toUnsignedString(this.hashCode(), 16));
  }
}
