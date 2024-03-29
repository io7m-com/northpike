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


package com.io7m.northpike.tests.server.scheduling;

import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPAssignmentsPagedType;
import com.io7m.northpike.database.api.NPCommitSummaryPagedType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.CommitsNotExecutedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.SearchType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.server.internal.assignments.NPAssignmentServiceType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.server.internal.schedule.NPScheduler;
import com.io7m.northpike.server.internal.schedule.NPSchedulerExecute;
import com.io7m.northpike.server.internal.schedule.NPSchedulerScheduled;
import com.io7m.northpike.server.internal.schedule.NPSchedulerType;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.tests.plans.NPFakeClock;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.Times;

import java.io.IOException;
import java.time.Instant;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;

public final class NPSchedulerTest
{
  private NPClockServiceType clock;
  private NPEventServiceType events;
  private NPDatabaseType database;
  private NPRepositoryServiceType repositories;
  private NPAssignmentServiceType assignments;
  private NPFakeClock fakeClock;
  private NPSchedulerType scheduler;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private SearchType assignmentSearch;
  private NPAssignmentsPagedType assignmentsPaged;
  private CommitsNotExecutedType commitsNotExecuted;
  private NPCommitSummaryPagedType commitsPaged;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.fakeClock =
      new NPFakeClock();
    this.clock =
      new NPClock(this.fakeClock);
    this.events =
      Mockito.mock(NPEventServiceType.class);
    this.database =
      Mockito.mock(NPDatabaseType.class);
    this.assignments =
      Mockito.mock(NPAssignmentServiceType.class);
    this.repositories =
      Mockito.mock(NPRepositoryServiceType.class);
    this.connection =
      Mockito.mock(NPDatabaseConnectionType.class);
    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);

    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);
    Mockito.when(this.database.openConnection(any()))
      .thenReturn(this.connection);

    this.assignmentsPaged =
      Mockito.mock(NPAssignmentsPagedType.class);
    this.assignmentSearch =
      Mockito.mock(SearchType.class);
    this.commitsNotExecuted =
      Mockito.mock(CommitsNotExecutedType.class);
    this.commitsPaged =
      Mockito.mock(NPCommitSummaryPagedType.class);

    Mockito.when(this.assignmentSearch.execute(any()))
      .thenReturn(this.assignmentsPaged);
    Mockito.when(this.transaction.queries(SearchType.class))
      .thenReturn(this.assignmentSearch);
    Mockito.when(this.transaction.queries(CommitsNotExecutedType.class))
      .thenReturn(this.commitsNotExecuted);
    Mockito.when(this.commitsNotExecuted.execute(any()))
      .thenReturn(this.commitsPaged);
  }

  /**
   * With no assignments, nothing happens.
   *
   * @throws Exception On errors
   */

  @Test
  public void testNoAssignments()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.scheduler.tick();

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * If assignments can't be fetched, nothing happens.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentsFetchFailure()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    Mockito.when(this.assignmentSearch.execute(any()))
      .thenThrow(new NPDatabaseException(
        "Ouch",
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      ));

    this.scheduler.tick();

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Only assignments with a timed schedule are scheduled.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentNotScheduled()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            new NPRepositoryID(UUID.randomUUID()),
            NPPlanIdentifier.of("y", 23L),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.scheduler.tick();

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Assignments that are scheduled past the point where they _would_ have
   * been executed are scheduled to happen in the next hour.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledLate()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:59:23+00:00");

    this.setupCommitsForExecution(repositoryId);
    this.scheduler.tick();

    Mockito.verify(this.repositories, new Times(1))
      .checkOne(eq(repositoryId));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("a")
      )));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("b")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerScheduled(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2001-01-01T00:02:00+00:00")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerExecute(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
      )));

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Assignments that are already schedules aren't scheduled again.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledRedundant()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.setupCommitsForExecution(repositoryId);

    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:02:00+00:00");

    this.scheduler.tick();
    this.scheduler.tick();

    Mockito.verify(this.repositories, new Times(1))
      .checkOne(eq(repositoryId));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("a")
      )));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("b")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerScheduled(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2001-01-01T00:02:00+00:00")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerExecute(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
      )));

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Scheduled assignments are executed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledExecuted()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.scheduler.tick();

    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:02:00+00:00");

    this.setupCommitsForExecution(repositoryId);

    this.scheduler.tick();

    Mockito.verify(this.repositories, new Times(1))
      .checkOne(eq(repositoryId));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("a")
      )));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("b")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerScheduled(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2001-01-01T00:02:00+00:00")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerExecute(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
      )));

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  private void setupCommitsForExecution(NPRepositoryID repositoryId)
    throws NPDatabaseException
  {
    final var future = new CompletableFuture<Void>();
    future.complete(null);

    Mockito.when(this.repositories.checkOne(eq(repositoryId)))
      .thenReturn(future);

    Mockito.when(this.commitsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPCommitSummary(
            new NPCommitID(repositoryId, new NPCommitUnqualifiedID("a")),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            "Commit 0"
          ),
          new NPCommitSummary(
            new NPCommitID(repositoryId, new NPCommitUnqualifiedID("b")),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            "Commit 1"
          )
        ), 0, 1, 0L
      ));

    Mockito.when(this.commitsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));
  }

  /**
   * Scheduled assignments are executed even if they miss their starting time.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledExecutedLate()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.scheduler.tick();

    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:03:00+00:00");

    Mockito.when(this.repositories.checkOne(any()))
      .thenReturn(CompletableFuture.completedFuture(null));

    Mockito.when(this.commitsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPCommitSummary(
            new NPCommitID(repositoryId, new NPCommitUnqualifiedID("a")),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            "Commit 0"
          ),
          new NPCommitSummary(
            new NPCommitID(repositoryId, new NPCommitUnqualifiedID("b")),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            OffsetDateTime.parse("2000-01-01T00:00:00+00:00"),
            "Commit 1"
          )
        ), 0, 1, 0L
      ));

    Mockito.when(this.commitsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.scheduler.tick();

    Mockito.verify(this.repositories, new Times(1))
      .checkOne(eq(repositoryId));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("a")
      )));

    Mockito.verify(this.assignments, new Times(1))
      .requestExecution(eq(new NPAssignmentExecutionRequest(
        NPAssignmentName.of("x"),
        new NPCommitUnqualifiedID("b")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerScheduled(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2001-01-01T00:02:00+00:00")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerExecute(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
      )));

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Scheduled assignments are not executed early.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledExecutedNotEarly()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.scheduler.tick();

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Scheduled assignments are not executed if the repository cannot be updated.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledExecutedRepositoryFails()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:02:00+00:00");

    this.setupCommitsForExecution(repositoryId);

    Mockito.when(this.repositories.checkOne(any()))
      .thenReturn(CompletableFuture.failedFuture(new IOException("Ouch!")));

    this.scheduler.tick();

    Mockito.verify(this.repositories, new Times(1))
      .checkOne(eq(repositoryId));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerScheduled(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2001-01-01T00:02:00+00:00")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerExecute(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
      )));

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }

  /**
   * Scheduled assignments are not executed if the commits cannot be retrieved.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAssignmentScheduledExecutedCommitsFails()
    throws Exception
  {
    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:00:00+00:00");

    this.scheduler =
      NPScheduler.create(
        this.clock,
        this.events,
        this.database,
        this.repositories,
        this.assignments
      );

    assertEquals(
      120,
      NPAssignmentName.of("x").hashCode()
    );

    final var repositoryId =
      new NPRepositoryID(UUID.randomUUID());

    Mockito.when(this.assignmentsPaged.pageCurrent(any()))
      .thenReturn(new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x"),
            repositoryId,
            NPPlanIdentifier.of("y", 23L),
            new NPAssignmentScheduleHourlyHashed(
              OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
            )
          )
        ), 0, 1, 0L
      ));
    Mockito.when(this.assignmentsPaged.pageNext(any()))
      .thenReturn(new NPPage<>(
        List.of(), 0, 1, 0L
      ));

    final var future = new CompletableFuture<Void>();
    future.complete(null);

    Mockito.when(this.repositories.checkOne(eq(repositoryId)))
      .thenReturn(future);

    Mockito.when(this.commitsNotExecuted.execute(any()))
      .thenThrow(new NPDatabaseException(
        "No!",
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      ));

    this.fakeClock.timeNow =
      Instant.parse("2001-01-01T00:02:00+00:00");

    this.scheduler.tick();

    Mockito.verify(this.repositories, new Times(1))
      .checkOne(eq(repositoryId));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerScheduled(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2001-01-01T00:02:00+00:00")
      )));

    Mockito.verify(this.events, new Times(1))
      .emit(eq(new NPSchedulerExecute(
        NPAssignmentName.of("x"),
        OffsetDateTime.parse("2000-01-01T00:00:00+00:00")
      )));

    Mockito.verifyNoMoreInteractions(this.events);
    Mockito.verifyNoMoreInteractions(this.assignments);
    Mockito.verifyNoMoreInteractions(this.repositories);
  }
}
