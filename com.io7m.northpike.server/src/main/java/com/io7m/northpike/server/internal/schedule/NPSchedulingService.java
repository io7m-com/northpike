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


package com.io7m.northpike.server.internal.schedule;


import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.server.internal.assignments.NPAssignmentServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import io.opentelemetry.api.trace.SpanKind;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * A service that schedules assignment executions.
 */

public final class NPSchedulingService
  implements NPSchedulingServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPSchedulingService.class);

  private final ExecutorService executor;
  private final NPTelemetryServiceType telemetry;
  private final NPSchedulerType scheduler;
  private final AtomicBoolean closed;
  private final CompletableFuture<Void> waitSchedule;

  private NPSchedulingService(
    final ExecutorService inExecutor,
    final NPClockServiceType inClock,
    final NPTelemetryServiceType inTelemetry,
    final NPDatabaseType inDatabase,
    final NPEventServiceType inEvents,
    final NPRepositoryServiceType inRepositories,
    final NPAssignmentServiceType inAssignments)
  {
    this.executor =
      Objects.requireNonNull(inExecutor, "executor");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");

    this.scheduler =
      NPScheduler.create(
        inClock,
        inEvents,
        inDatabase,
        inRepositories,
        inAssignments
      );

    this.closed =
      new AtomicBoolean(false);
    this.waitSchedule =
      new CompletableFuture<>();
  }

  /**
   * A service that schedules assignment executions.
   *
   * @param clock         The clock
   * @param telemetry     The telemetry service
   * @param configuration The configuration service
   * @param events        The event service
   * @param database      The database
   * @param repositories  The repository service
   * @param assignments   The assignment service
   *
   * @return The service
   */

  public static NPSchedulingServiceType create(
    final NPClockServiceType clock,
    final NPTelemetryServiceType telemetry,
    final NPConfigurationServiceType configuration,
    final NPEventServiceType events,
    final NPDatabaseType database,
    final NPRepositoryServiceType repositories,
    final NPAssignmentServiceType assignments)
  {
    Objects.requireNonNull(clock, "clock");
    Objects.requireNonNull(configuration, "configuration");
    Objects.requireNonNull(database, "database");
    Objects.requireNonNull(telemetry, "telemetry");
    Objects.requireNonNull(events, "events");
    Objects.requireNonNull(repositories, "repositories");
    Objects.requireNonNull(assignments, "assignments");

    final var executor =
      Executors.newThreadPerTaskExecutor(
        Thread.ofVirtual()
          .name("com.io7m.northpike.scheduling-", 0L)
          .factory()
      );

    final var schedulingService =
      new NPSchedulingService(
        executor,
        clock,
        telemetry,
        database,
        events,
        repositories,
        assignments
      );

    executor.execute(schedulingService::runScheduleTask);
    return schedulingService;
  }

  private void runScheduleTask()
  {
    final var scheduleInterval =
      Duration.ofSeconds(10L);

    while (!this.closed.get()) {
      try {
        this.runSchedule();
      } catch (final Exception e) {
        // Not important.
      }

      try {
        this.waitSchedule.get(scheduleInterval.toSeconds(), TimeUnit.SECONDS);
      } catch (final Exception e) {
        // Not a problem.
      }
    }
  }

  private void runSchedule()
  {
    LOG.debug("Scheduling task starting");

    final var span =
      this.telemetry.tracer()
        .spanBuilder("Schedule")
        .setSpanKind(SpanKind.INTERNAL)
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.scheduler.tick();
    } catch (final Exception e) {
      LOG.error("Scheduling task failed: ", e);
      span.recordException(e);
    } finally {
      span.end();
    }
  }

  @Override
  public String description()
  {
    return "Server scheduling service.";
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.waitSchedule.complete(null);
      this.executor.close();
    }
  }

  @Override
  public String toString()
  {
    return "[NPSchedulingService 0x%s]"
      .formatted(Long.toUnsignedString(this.hashCode(), 16));
  }
}
