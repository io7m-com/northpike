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
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;

import java.time.OffsetDateTime;

import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CANCELLED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CREATED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_RUNNING;

/**
 * Mark all non-completed assignment executions as cancelled.
 */

public final class NPDBQAssignmentExecutionsCancelAll
  extends NPDBQAbstract<NPDatabaseUnit, Long>
  implements NPDatabaseQueriesAssignmentsType.ExecutionsCancelAllType
{
  private static final Service<NPDatabaseUnit, Long, ExecutionsCancelAllType> SERVICE =
    new Service<>(
      ExecutionsCancelAllType.class,
      NPDBQAssignmentExecutionsCancelAll::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionsCancelAll(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Long onExecute(
    final DSLContext context,
    final NPDatabaseUnit parameters)
    throws NPDatabaseException
  {
    final var timeNow =
      OffsetDateTime.now(
        this.transaction()
          .connection()
          .database()
          .clock()
      );

    final var applicable =
      ASSIGNMENT_EXECUTIONS.AE_STATUS.eq(ASSIGNMENT_EXECUTION_CREATED)
        .or(ASSIGNMENT_EXECUTIONS.AE_STATUS.eq(ASSIGNMENT_EXECUTION_RUNNING));

    return Long.valueOf((long) context.update(ASSIGNMENT_EXECUTIONS)
      .set(ASSIGNMENT_EXECUTIONS.AE_ENDED, timeNow)
      .set(ASSIGNMENT_EXECUTIONS.AE_STATUS, ASSIGNMENT_EXECUTION_CANCELLED)
      .where(applicable)
      .execute());
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }
}
