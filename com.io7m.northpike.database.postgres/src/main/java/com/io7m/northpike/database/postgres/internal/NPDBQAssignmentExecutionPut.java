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
import com.io7m.northpike.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateCancelled;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;
import org.jooq.Record1;
import org.jooq.Select;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CANCELLED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CREATED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CREATION_FAILED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_FAILED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_REQUESTED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_RUNNING;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_SUCCEEDED;

/**
 * Update an assignment execution.
 */

public final class NPDBQAssignmentExecutionPut
  extends NPDBQAbstract<NPAssignmentExecutionStateType, NPDatabaseUnit>
  implements NPDatabaseQueriesAssignmentsType.ExecutionPutType
{
  private static final Service<NPAssignmentExecutionStateType, NPDatabaseUnit, ExecutionPutType> SERVICE =
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

  private static NPDatabaseUnit onExecuteStateCreationFailed(
    final DSLContext context,
    final NPAssignmentExecutionStateCreationFailed r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_STATUS,
          ASSIGNMENT_EXECUTION_CREATION_FAILED)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_STATUS,
          ASSIGNMENT_EXECUTION_CREATION_FAILED);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static NPDatabaseUnit onExecuteStateSucceeded(
    final DSLContext context,
    final NPAssignmentExecutionStateSucceeded r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, r.timeEnded())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_SUCCEEDED)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, r.timeEnded())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_SUCCEEDED);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static NPDatabaseUnit onExecuteStateFailed(
    final DSLContext context,
    final NPAssignmentExecutionStateFailed r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, r.timeEnded())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_FAILED)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, r.timeEnded())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_FAILED);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static Select<Record1<Long>> selectCommit(
    final DSLContext context,
    final NPAssignmentExecution execution)
  {
    final var commit =
      execution.commit();
    final var repositoryId =
      execution.assignment().repositoryId();

    return context.select(REPOSITORY_COMMITS.RC_ID)
      .from(REPOSITORY_COMMITS)
      .where(
        REPOSITORY_COMMITS.RC_REPOSITORY.eq(repositoryId)
          .and(REPOSITORY_COMMITS.RC_COMMIT_ID.eq(commit.value()))
      );
  }

  private static Select<Record1<Long>> selectAssignment(
    final DSLContext context,
    final NPAssignmentExecutionRequest request)
  {
    return context.select(ASSIGNMENTS.A_ID)
      .from(ASSIGNMENTS)
      .where(ASSIGNMENTS.A_NAME.eq(request.assignment().toString()));
  }

  private static NPDatabaseUnit onExecuteStateRunning(
    final DSLContext context,
    final NPAssignmentExecutionStateRunning r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_RUNNING)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_RUNNING);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static NPDatabaseUnit onExecuteStateCreated(
    final DSLContext context,
    final NPAssignmentExecutionStateCreated r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_CREATED)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT,
          selectAssignment(context, r.request()))
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(
          ASSIGNMENT_EXECUTIONS.AE_COMMIT,
          selectCommit(context, r.execution()))
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_CREATED);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static NPDatabaseUnit onExecuteStateRequested(
    final DSLContext context,
    final NPAssignmentExecutionStateRequested r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_REQUESTED)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_REQUESTED);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  private static NPDatabaseUnit onExecuteStateCancelled(
    final DSLContext context,
    final NPAssignmentExecutionStateCancelled r)
  {
    final var request = r.request();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTIONS)
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, r.timeEnded())
        .set(ASSIGNMENT_EXECUTIONS.AE_ID, r.id())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_CANCELLED)
        .onConflictOnConstraint(DSL.name("assignment_executions_primary_key"))
        .doUpdate()
        .set(
          ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
          request.assignment().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME, request.commit().toString())
        .set(ASSIGNMENT_EXECUTIONS.AE_CREATED, r.timeCreated())
        .set(ASSIGNMENT_EXECUTIONS.AE_STARTED, r.timeStarted())
        .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, r.timeEnded())
        .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_CANCELLED);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPAssignmentExecutionStateType execution)
  {
    if (execution instanceof final NPAssignmentExecutionStateRequested r) {
      return onExecuteStateRequested(context, r);
    }
    if (execution instanceof final NPAssignmentExecutionStateCreationFailed r) {
      return onExecuteStateCreationFailed(context, r);
    }
    if (execution instanceof final NPAssignmentExecutionStateCreated r) {
      return onExecuteStateCreated(context, r);
    }
    if (execution instanceof final NPAssignmentExecutionStateRunning r) {
      return onExecuteStateRunning(context, r);
    }
    if (execution instanceof final NPAssignmentExecutionStateSucceeded r) {
      return onExecuteStateSucceeded(context, r);
    }
    if (execution instanceof final NPAssignmentExecutionStateFailed r) {
      return onExecuteStateFailed(context, r);
    }
    if (execution instanceof final NPAssignmentExecutionStateCancelled r) {
      return onExecuteStateCancelled(context, r);
    }

    throw new IllegalStateException(
      "Unrecognized state: %s".formatted(execution)
    );
  }
}
