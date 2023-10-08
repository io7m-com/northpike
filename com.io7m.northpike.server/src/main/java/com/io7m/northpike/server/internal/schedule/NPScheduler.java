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
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.CommitsNotExecutedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.SearchType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPTimeRange;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.server.internal.assignments.NPAssignmentServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;

/**
 * The default scheduler.
 */

public final class NPScheduler implements NPSchedulerType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPScheduler.class);

  private final NPClockServiceType clock;
  private final HashMap<NPAssignmentName, AssignmentScheduled> assignmentsScheduled;
  private final NPEventServiceType events;
  private final NPDatabaseType database;
  private final NPRepositoryServiceType repositoryService;
  private final NPAssignmentServiceType assignmentService;
  private OffsetDateTime timeNow;

  private NPScheduler(
    final NPClockServiceType inClock,
    final NPEventServiceType inEvents,
    final NPDatabaseType inDatabase,
    final NPRepositoryServiceType inRepositories,
    final NPAssignmentServiceType inAssignments)
  {
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.repositoryService =
      Objects.requireNonNull(inRepositories, "repositories");
    this.assignmentService =
      Objects.requireNonNull(inAssignments, "assignments");

    this.assignmentsScheduled =
      new HashMap<>();
    this.timeNow =
      this.clock.now();
  }

  /**
   * The default scheduler.
   *
   * @param inClock        The clock service
   * @param inDatabase     The database
   * @param inAssignments  The assignment service
   * @param inEvents       The event service
   * @param inRepositories The repository service
   *
   * @return A scheduler
   */

  public static NPSchedulerType create(
    final NPClockServiceType inClock,
    final NPEventServiceType inEvents,
    final NPDatabaseType inDatabase,
    final NPRepositoryServiceType inRepositories,
    final NPAssignmentServiceType inAssignments)
  {
    return new NPScheduler(
      inClock,
      inEvents,
      inDatabase,
      inRepositories,
      inAssignments
    );
  }

  private record AssignmentScheduled(
    NPAssignment assignment,
    OffsetDateTime time,
    OffsetDateTime commitAgeCutoff)
  {
    private AssignmentScheduled
    {
      Objects.requireNonNull(assignment, "assignment");
      Objects.requireNonNull(time, "time");
      Objects.requireNonNull(commitAgeCutoff, "commitAgeCutoff");
    }
  }

  @Override
  public void tick()
  {
    this.timeNow = this.clock.now();
    if (this.timeNow.getSecond() == 0) {
      this.scheduleAssignments();
    }

    this.executeAssignments();
  }

  private void executeAssignments()
  {
    final var scheduled =
      Set.copyOf(this.assignmentsScheduled.values());

    for (final var assignment : scheduled) {
      if (!this.timeNow.isBefore(assignment.time)) {
        this.executeAssignment(assignment);
      }
    }
  }

  private void executeAssignment(
    final AssignmentScheduled assignment)
  {
    this.assignmentsScheduled.remove(assignment.assignment.name());

    this.events.emit(new NPSchedulerExecute(
      assignment.assignment.name(),
      assignment.commitAgeCutoff
    ));

    try {
      this.repositoryService.checkOne(assignment.assignment().repositoryId())
        .get(1L, TimeUnit.MINUTES);
    } catch (final Exception e) {
      NPTelemetryServiceType.recordSpanException(e);
      LOG.error("Failed to update repository: ", e);
      return;
    }

    final Set<NPCommitUnqualifiedID> commits;
    try {
      commits = this.onRetrieveUnbuiltCommitsFor(
        assignment.assignment,
        new NPTimeRange(
          assignment.commitAgeCutoff,
          this.timeNow.plusDays(1L)
        )
      );
    } catch (final Exception e) {
      NPTelemetryServiceType.recordSpanException(e);
      LOG.error("Failed to retrieve commits: ", e);
      return;
    }

    for (final var commit : commits) {
      this.assignmentService.requestExecution(
        new NPAssignmentExecutionRequest(
          assignment.assignment().name(),
          commit
        )
      );
    }
  }

  private void scheduleAssignments()
  {
    final Set<NPAssignment> assignments;
    try {
      assignments = this.onRetrieveCurrentAssignments();
    } catch (final NPException e) {
      NPTelemetryServiceType.recordSpanException(e);
      LOG.error("Failed to retrieve assignments: ", e);
      return;
    }

    for (final var assignment : assignments) {
      this.scheduleAssignment(assignment);
    }
  }

  private void scheduleAssignment(
    final NPAssignment assignment)
  {
    final var schedule = assignment.schedule();
    if (schedule instanceof NPAssignmentScheduleNone) {
      return;
    }

    if (schedule instanceof final NPAssignmentScheduleHourlyHashed hashed) {
      this.scheduleAssignmentHourlyHashed(assignment, hashed);
      return;
    }

    throw new IllegalStateException(
      "Unrecognized schedule: %s".formatted(schedule)
    );
  }

  private void scheduleAssignmentHourlyHashed(
    final NPAssignment assignment,
    final NPAssignmentScheduleHourlyHashed hashed)
  {
    if (this.assignmentsScheduled.containsKey(assignment.name())) {
      return;
    }

    /*
     * Get the time at the start of the current hour, and the time at the
     * start of the next hour. The assignment will be scheduled based whichever
     * one results in a time that is in the future.
     */

    final var timeHourStart =
      this.timeNow.withMinute(0)
        .withSecond(0)
        .withNano(0);

    final var timeHourNext =
      timeHourStart.plusHours(1L);

    /*
     * The offset from the start of the hour is the hash of the assignment
     * name modulo the number of seconds in an hour.
     */

    final var seconds =
      (long) (assignment.name().toString().hashCode()) % 3600L;

    final var time0 =
      timeHourStart.plusSeconds(seconds);
    final var time1 =
      timeHourNext.plusSeconds(seconds);

    final OffsetDateTime timeTarget;
    if (time0.isBefore(this.timeNow)) {
      timeTarget = time1;
    } else {
      timeTarget = time0;
    }

    final var task =
      new AssignmentScheduled(
        assignment,
        timeTarget,
        hashed.commitAgeCutoff()
      );

    this.assignmentsScheduled.put(task.assignment.name(), task);

    this.events.emit(
      new NPSchedulerScheduled(task.assignment.name(), timeTarget)
    );
  }

  private Set<NPAssignment> onRetrieveCurrentAssignments()
    throws NPException
  {
    final var assignments = new HashSet<NPAssignment>();
    try (var connection = this.database.openConnection(NORTHPIKE_READ_ONLY)) {
      try (var transaction = connection.openTransaction()) {
        final var paged =
          transaction.queries(SearchType.class)
            .execute(
              new NPAssignmentSearchParameters(
                Optional.empty(),
                Optional.empty(),
                new NPComparisonFuzzyType.Anything<>(),
                1000L
              )
            );

        var page = paged.pageCurrent(transaction);
        for (int pageIndex = 0; pageIndex < page.pageCount(); ++pageIndex) {
          assignments.addAll(page.items());
          page = paged.pageNext(transaction);
        }
      }
    }
    return assignments;
  }

  private Set<NPCommitUnqualifiedID> onRetrieveUnbuiltCommitsFor(
    final NPAssignment assignment,
    final NPTimeRange timeRange)
    throws NPException
  {
    final var commits = new HashSet<NPCommitUnqualifiedID>();
    try (var connection = this.database.openConnection(NORTHPIKE_READ_ONLY)) {
      try (var transaction = connection.openTransaction()) {
        final var paged =
          transaction.queries(CommitsNotExecutedType.class)
            .execute(
              new CommitsNotExecutedType.Parameters(
                assignment.name(),
                timeRange,
                1000L
              )
            );

        var page = paged.pageCurrent(transaction);
        for (int pageIndex = 0; pageIndex < page.pageCount(); ++pageIndex) {
          commits.addAll(
            page.items()
              .stream()
              .map(x -> x.id().commitId())
              .collect(Collectors.toUnmodifiableSet())
          );
          page = paged.pageNext(transaction);
        }
      }
    }
    return commits;
  }
}
