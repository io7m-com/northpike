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


package com.io7m.northpike.database.postgres.internal;


import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentExecution;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCancelled;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import org.jooq.DSLContext;
import org.jooq.Record;

import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.NPDBQAssignmentGet.mapSchedule;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;

/**
 * Retrieve an assignment execution.
 */

public final class NPDBQAssignmentExecutionGet
  extends NPDBQAbstract<NPAssignmentExecutionID, Optional<NPAssignmentExecutionStateType>>
  implements AssignmentExecutionGetType
{
  private static final Service<
    NPAssignmentExecutionID,
    Optional<NPAssignmentExecutionStateType>,
    AssignmentExecutionGetType> SERVICE =
    new Service<>(AssignmentExecutionGetType.class, NPDBQAssignmentExecutionGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPAssignmentExecutionStateType> onExecute(
    final DSLContext context,
    final NPAssignmentExecutionID name)
    throws NPDatabaseException
  {
    return context.select(
        ASSIGNMENTS.A_NAME,
        ASSIGNMENTS.A_REPOSITORY,
        ASSIGNMENTS.A_SCHEDULE,
        ASSIGNMENTS.A_SCHEDULE_COMMIT_AGE_CUTOFF,
        ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
        ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME,
        ASSIGNMENT_EXECUTIONS.AE_CREATED,
        ASSIGNMENT_EXECUTIONS.AE_ENDED,
        ASSIGNMENT_EXECUTIONS.AE_ID,
        ASSIGNMENT_EXECUTIONS.AE_STARTED,
        ASSIGNMENT_EXECUTIONS.AE_STATUS,
        PLANS.P_NAME,
        PLANS.P_VERSION
      ).from(ASSIGNMENT_EXECUTIONS)
      .leftOuterJoin(ASSIGNMENTS)
      .on(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT.eq(ASSIGNMENTS.A_ID))
      .leftOuterJoin(PLANS)
      .on(ASSIGNMENTS.A_PLAN.eq(PLANS.P_ID))
      .where(ASSIGNMENT_EXECUTIONS.AE_ID.eq(name.value()))
      .fetchOptional()
      .map(NPDBQAssignmentExecutionGet::mapAssignmentExecutionRecord);
  }

  static NPAssignmentExecutionStateType mapAssignmentExecutionRecord(
    final org.jooq.Record r)
  {
    final var state = r.get(ASSIGNMENT_EXECUTIONS.AE_STATUS);
    return switch (state) {
      case ASSIGNMENT_EXECUTION_REQUESTED -> mapStateRequested(r);
      case ASSIGNMENT_EXECUTION_CREATION_FAILED -> mapStateCreationFailed(r);
      case ASSIGNMENT_EXECUTION_CREATED -> mapStateCreated(r);
      case ASSIGNMENT_EXECUTION_RUNNING -> mapStateRunning(r);
      case ASSIGNMENT_EXECUTION_SUCCEEDED -> mapStateSucceeded(r);
      case ASSIGNMENT_EXECUTION_FAILED -> mapStateFailed(r);
      case ASSIGNMENT_EXECUTION_CANCELLED -> mapStateCancelled(r);
    };
  }

  private static NPAssignmentExecutionStateCancelled mapStateCancelled(
    final Record r)
  {
    return new NPAssignmentExecutionStateCancelled(
      new NPAssignmentExecutionID(r.get(ASSIGNMENT_EXECUTIONS.AE_ID)),
      mapRequest(r),
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
      r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED),
      r.get(ASSIGNMENT_EXECUTIONS.AE_ENDED)
    );
  }

  private static NPAssignmentExecutionStateFailed mapStateFailed(
    final Record r)
  {
    return new NPAssignmentExecutionStateFailed(
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
      mapExecution(r),
      r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED),
      r.get(ASSIGNMENT_EXECUTIONS.AE_ENDED)
    );
  }

  private static NPAssignmentExecutionStateSucceeded mapStateSucceeded(
    final Record r)
  {
    return new NPAssignmentExecutionStateSucceeded(
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
      mapExecution(r),
      r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED),
      r.get(ASSIGNMENT_EXECUTIONS.AE_ENDED)
    );
  }

  private static NPAssignmentExecutionStateRunning mapStateRunning(
    final Record r)
  {
    return new NPAssignmentExecutionStateRunning(
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
      mapExecution(r),
      r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED)
    );
  }

  private static NPAssignmentExecutionStateCreated mapStateCreated(
    final Record r)
  {
    return new NPAssignmentExecutionStateCreated(
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
      mapExecution(r)
    );
  }

  private static NPAssignmentExecution mapExecution(
    final Record r)
  {
    return new NPAssignmentExecution(
      new NPAssignmentExecutionID(r.get(ASSIGNMENT_EXECUTIONS.AE_ID)),
      new NPAssignment(
        NPAssignmentName.of(r.get(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME)),
        new NPRepositoryID(r.get(ASSIGNMENTS.A_REPOSITORY)),
        NPPlanIdentifier.of(
          r.get(PLANS.P_NAME),
          r.<Long>get(PLANS.P_VERSION).longValue()
        ),
        mapSchedule(r)
      ),
      new NPCommitUnqualifiedID(r.get(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME))
    );
  }

  private static NPAssignmentExecutionStateCreationFailed mapStateCreationFailed(
    final Record r)
  {
    return new NPAssignmentExecutionStateCreationFailed(
      new NPAssignmentExecutionID(r.get(ASSIGNMENT_EXECUTIONS.AE_ID)),
      mapRequest(r),
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED)
    );
  }

  private static NPAssignmentExecutionRequest mapRequest(final Record r)
  {
    return new NPAssignmentExecutionRequest(
      NPAssignmentName.of(r.get(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME)),
      new NPCommitUnqualifiedID(r.get(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME))
    );
  }

  private static NPAssignmentExecutionStateRequested mapStateRequested(
    final Record r)
  {
    return new NPAssignmentExecutionStateRequested(
      new NPAssignmentExecutionID(r.get(ASSIGNMENT_EXECUTIONS.AE_ID)),
      mapRequest(r),
      r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED)
    );
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }
}
