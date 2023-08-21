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


import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.assignments.NPAssignmentExecution;
import com.io7m.northpike.assignments.NPAssignmentExecutionCreated;
import com.io7m.northpike.assignments.NPAssignmentExecutionFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionRunning;
import com.io7m.northpike.assignments.NPAssignmentExecutionStatusType;
import com.io7m.northpike.assignments.NPAssignmentExecutionSucceeded;
import com.io7m.northpike.assignments.NPAssignmentName;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanName;
import org.jooq.DSLContext;
import org.jooq.Record;

import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;

/**
 * Retrieve an archive.
 */

public final class NPDBQAssignmentExecutionGet
  extends NPDBQAbstract<UUID, Optional<NPAssignmentExecution>>
  implements NPDatabaseQueriesAssignmentsType.ExecutionGetType
{
  private static final Service<UUID, Optional<NPAssignmentExecution>, ExecutionGetType> SERVICE =
    new Service<>(ExecutionGetType.class, NPDBQAssignmentExecutionGet::new);

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
  protected Optional<NPAssignmentExecution> onExecute(
    final DSLContext context,
    final UUID name)
    throws NPDatabaseException
  {
    return context.select(
      ASSIGNMENT_EXECUTIONS.AE_ID,
      ASSIGNMENT_EXECUTIONS.AE_STATUS,
      ASSIGNMENT_EXECUTIONS.AE_CREATED,
      ASSIGNMENT_EXECUTIONS.AE_STARTED,
      ASSIGNMENT_EXECUTIONS.AE_ENDED,
      ASSIGNMENTS.A_NAME,
      ASSIGNMENTS.A_REPOSITORY,
      PLANS.P_NAME,
      PLANS.P_VERSION,
      REPOSITORY_COMMITS.RC_COMMIT_ID
    ).from(ASSIGNMENT_EXECUTIONS)
      .join(ASSIGNMENTS)
      .on(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT.eq(ASSIGNMENTS.A_ID))
      .join(PLANS)
      .on(ASSIGNMENTS.A_PLAN.eq(PLANS.P_ID))
      .join(REPOSITORY_COMMITS)
      .on(ASSIGNMENT_EXECUTIONS.AE_COMMIT.eq(REPOSITORY_COMMITS.RC_ID))
      .where(ASSIGNMENT_EXECUTIONS.AE_ID.eq(name))
      .fetchOptional()
      .map(NPDBQAssignmentExecutionGet::mapRecord);
  }

  private static NPAssignmentExecution mapRecord(
    final org.jooq.Record r)
  {
    return new NPAssignmentExecution(
      r.get(ASSIGNMENT_EXECUTIONS.AE_ID),
      new NPAssignment(
        NPAssignmentName.of(r.get(ASSIGNMENTS.A_NAME)),
        r.get(ASSIGNMENTS.A_REPOSITORY),
        new NPPlanIdentifier(
          NPPlanName.of(r.get(PLANS.P_NAME)),
          r.<Long>get(PLANS.P_VERSION).longValue()
        )
      ),
      new NPCommitID(
        r.get(ASSIGNMENTS.A_REPOSITORY),
        r.get(REPOSITORY_COMMITS.RC_COMMIT_ID)
      ),
      mapStatus(r)
    );
  }

  private static NPAssignmentExecutionStatusType mapStatus(
    final Record r)
  {
    return switch (r.get(ASSIGNMENT_EXECUTIONS.AE_STATUS)) {
      case ASSIGNMENT_EXECUTION_RUNNING -> {
        yield new NPAssignmentExecutionRunning(
          r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
          r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED)
        );
      }
      case ASSIGNMENT_EXECUTION_SUCCEEDED -> {
        yield new NPAssignmentExecutionSucceeded(
          r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
          r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED),
          r.get(ASSIGNMENT_EXECUTIONS.AE_ENDED)
        );
      }
      case ASSIGNMENT_EXECUTION_FAILED -> {
        yield new NPAssignmentExecutionFailed(
          r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED),
          r.get(ASSIGNMENT_EXECUTIONS.AE_STARTED),
          r.get(ASSIGNMENT_EXECUTIONS.AE_ENDED)
        );
      }
      case ASSIGNMENT_EXECUTION_CREATED -> {
        yield new NPAssignmentExecutionCreated(
          r.get(ASSIGNMENT_EXECUTIONS.AE_CREATED)
        );
      }
    };
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }
}
