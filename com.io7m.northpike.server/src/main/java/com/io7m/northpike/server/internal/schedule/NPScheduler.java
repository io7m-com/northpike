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
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentCommitsNotExecutedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentSearchType;
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
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
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

  private OffsetDateTime timeNow;
  private OffsetDateTime timeThen;
  private final HashMap<NPAssignmentName, AssignmentScheduled> assignmentsThisHour;
  private final HashMap<NPAssignmentName, AssignmentScheduled> assignmentsThisMinute;
  private final HashMap<NPAssignmentName, AssignmentScheduled> assignmentsToExecuteNow;
  private final NPAssignmentServiceType assignmentService;
  private final NPClockServiceType clock;
  private final NPDatabaseType database;
  private final NPEventServiceType events;
  private final NPRepositoryServiceType repositoryService;

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

    this.assignmentsThisHour =
      new HashMap<>();
    this.assignmentsThisMinute =
      new HashMap<>();
    this.assignmentsToExecuteNow =
      new HashMap<>();

    this.timeThen =
      this.clock.now()
        .minusMinutes(1L)
        .minusHours(1L);
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
    try {
      if (this.startingNewHour()) {
        this.assignmentsThisHour.clear();
      }
      if (this.startingNewMinute()) {
        this.assignmentsThisMinute.clear();
        this.assignmentsToExecuteNow.clear();
      }

      this.scheduleAssignments();
      this.executeAssignments();
    } finally {
      this.timeThen = this.timeNow;
    }
  }

  private boolean startingNewMinute()
  {
    return this.timeNow.getMinute() != this.timeThen.getMinute();
  }

  private boolean startingNewHour()
  {
    return this.timeNow.getHour() != this.timeThen.getHour();
  }

  private void executeAssignments()
  {
    final var scheduled =
      Set.copyOf(this.assignmentsToExecuteNow.values());

    for (final var assignment : scheduled) {
      this.executeAssignment(assignment);
    }
  }

  private void executeAssignment(
    final AssignmentScheduled assignment)
  {
    try {
      this.events.emit(new NPSchedulerExecute(
        assignment.assignment.name(),
        assignment.commitAgeCutoff
      ));

      try {
        this.repositoryService.repositoryUpdate(assignment.assignment().repositoryId())
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
    } finally {
      this.assignmentsToExecuteNow.remove(assignment.assignment.name());
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
    switch (schedule) {
      case final NPAssignmentScheduleNone ignored -> {
        // Nothing
      }
      case final NPAssignmentScheduleHourlyHashed hashed -> {
        this.scheduleAssignmentHourlyHashed(assignment, hashed);
      }
    }
  }

  private void scheduleAssignmentHourlyHashed(
    final NPAssignment assignment,
    final NPAssignmentScheduleHourlyHashed hashed)
  {
    if (this.haveAlreadyScheduled(assignment.name())) {
      return;
    }

    /*
     * Find the time at the start of the current hour.
     */

    final var timeHourStart =
      this.timeNow.withMinute(0)
        .withSecond(0)
        .withNano(0);

    /*
     * The offset from the start of the hour is the hash of the assignment
     * name modulo the number of seconds in an hour.
     */

    final var seconds =
      (long) (assignment.name().toString().hashCode()) % 3600L;

    final var timeTarget =
      timeHourStart.plusSeconds(seconds);

    /*
     * If the current time is after (or equal to) the target time, then
     * schedule an assignment. We are already protected from scheduling
     * assignments multiple times in the same hour or minute by the check above.
     */

    if (!this.timeNow.isBefore(timeTarget)) {
      final var task =
        new AssignmentScheduled(
          assignment,
          timeTarget,
          hashed.commitAgeCutoff()
        );

      this.scheduleNow(task, timeTarget);
    }
  }

  private void scheduleNow(
    final AssignmentScheduled task,
    final OffsetDateTime time)
  {
    this.assignmentsThisHour.put(task.assignment.name(), task);
    this.assignmentsThisMinute.put(task.assignment.name(), task);
    this.assignmentsToExecuteNow.put(task.assignment.name(), task);
    this.events.emit(new NPSchedulerScheduled(task.assignment.name(), time));
  }

  private boolean haveAlreadyScheduled(
    final NPAssignmentName name)
  {
    return this.haveAlreadyScheduledThisHour(name)
      || this.haveAlreadyScheduledThisMinute(name)
      || this.assignmentsToExecuteNow.containsKey(name);
  }

  private boolean haveAlreadyScheduledThisMinute(
    final NPAssignmentName name)
  {
    return this.assignmentsThisHour.containsKey(name);
  }

  private boolean haveAlreadyScheduledThisHour(
    final NPAssignmentName name)
  {
    return this.assignmentsThisMinute.containsKey(name);
  }

  private Set<NPAssignment> onRetrieveCurrentAssignments()
    throws NPException
  {
    final var assignments = new HashSet<NPAssignment>();
    try (var connection = this.database.openConnection(NORTHPIKE_READ_ONLY)) {
      try (var transaction = connection.openTransaction()) {
        final var paged =
          transaction.queries(AssignmentSearchType.class)
            .execute(
              new NPAssignmentSearchParameters(
                new NPComparisonExactType.Anything<>(),
                new NPComparisonExactType.Anything<>(),
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
          transaction.queries(AssignmentCommitsNotExecutedType.class)
            .execute(
              new AssignmentCommitsNotExecutedType.Parameters(
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
