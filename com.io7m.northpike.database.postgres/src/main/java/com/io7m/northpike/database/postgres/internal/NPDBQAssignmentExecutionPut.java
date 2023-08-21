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


import com.io7m.northpike.assignments.NPAssignmentExecution;
import com.io7m.northpike.assignments.NPAssignmentExecutionCreated;
import com.io7m.northpike.assignments.NPAssignmentExecutionFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionRunning;
import com.io7m.northpike.assignments.NPAssignmentExecutionStatusType;
import com.io7m.northpike.assignments.NPAssignmentExecutionSucceeded;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.Map;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CREATED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_FAILED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_RUNNING;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_SUCCEEDED;

/**
 * Update an assignment execution.
 */

public final class NPDBQAssignmentExecutionPut
  extends NPDBQAbstract<NPAssignmentExecution, NPDatabaseUnit>
  implements NPDatabaseQueriesAssignmentsType.ExecutionPutType
{
  private static final Service<NPAssignmentExecution, NPDatabaseUnit, ExecutionPutType> SERVICE =
    new Service<>(ExecutionPutType.class, NPDBQAssignmentExecutionPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionPut(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPAssignmentExecution execution)
  {
    final var vAssign =
      execution.assignment();

    final var assignment =
      context.select(ASSIGNMENTS.A_ID)
        .from(ASSIGNMENTS)
        .where(ASSIGNMENTS.A_NAME.eq(vAssign.name().toString()));

    final var vCommit =
      execution.commit();

    final var commit =
      context.select(REPOSITORY_COMMITS.RC_ID)
        .from(REPOSITORY_COMMITS)
        .where(
          REPOSITORY_COMMITS.RC_REPOSITORY.eq(vCommit.repository())
            .and(REPOSITORY_COMMITS.RC_COMMIT_ID.eq(vCommit.value()))
        );

    final var status =
      execution.status();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, execution.executionId())
        .set(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT, assignment)
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT, commit)
        .set(putStatusFields(status))
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, execution.executionId())
        .set(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT, assignment)
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT, commit)
        .set(putStatusFields(status));

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static Map<?, ?> putStatusFields(
    final NPAssignmentExecutionStatusType status)
  {
    if (status instanceof final NPAssignmentExecutionSucceeded succeeded) {
      return putSucceeded(succeeded);
    }
    if (status instanceof final NPAssignmentExecutionFailed failed) {
      return putFailed(failed);
    }
    if (status instanceof final NPAssignmentExecutionCreated created) {
      return putCreated(created);
    }
    if (status instanceof final NPAssignmentExecutionRunning started) {
      return putStarted(started);
    }

    throw new IllegalStateException(
      "Unrecognized status: %s".formatted(status)
    );
  }

  private static Map<?, ?> putStarted(
    final NPAssignmentExecutionRunning started)
  {
    final var m = new HashMap<>(4);
    m.put(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_RUNNING);
    m.put(ASSIGNMENT_EXECUTIONS.AE_CREATED, started.timeCreated());
    m.put(ASSIGNMENT_EXECUTIONS.AE_ENDED, (OffsetDateTime) null);
    m.put(ASSIGNMENT_EXECUTIONS.AE_STARTED, started.timeStarted());
    return m;
  }

  private static Map<?, ?> putCreated(
    final NPAssignmentExecutionCreated created)
  {
    final var m = new HashMap<>(4);
    m.put(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_CREATED);
    m.put(ASSIGNMENT_EXECUTIONS.AE_CREATED, created.timeCreated());
    m.put(ASSIGNMENT_EXECUTIONS.AE_ENDED, (OffsetDateTime) null);
    m.put(ASSIGNMENT_EXECUTIONS.AE_STARTED, (OffsetDateTime) null);
    return m;
  }

  private static Map<?, ?> putFailed(
    final NPAssignmentExecutionFailed failed)
  {
    final var m = new HashMap<>(4);
    m.put(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_FAILED);
    m.put(ASSIGNMENT_EXECUTIONS.AE_CREATED, failed.timeCreated());
    m.put(ASSIGNMENT_EXECUTIONS.AE_ENDED, failed.timeEnded());
    m.put(ASSIGNMENT_EXECUTIONS.AE_STARTED, failed.timeStarted());
    return m;
  }

  private static Map<?, ?> putSucceeded(
    final NPAssignmentExecutionSucceeded succeeded)
  {
    final var m = new HashMap<>(4);
    m.put(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_SUCCEEDED);
    m.put(ASSIGNMENT_EXECUTIONS.AE_CREATED, succeeded.timeCreated());
    m.put(ASSIGNMENT_EXECUTIONS.AE_ENDED, succeeded.timeEnded());
    m.put(ASSIGNMENT_EXECUTIONS.AE_STARTED, succeeded.timeStarted());
    return m;
  }
}
