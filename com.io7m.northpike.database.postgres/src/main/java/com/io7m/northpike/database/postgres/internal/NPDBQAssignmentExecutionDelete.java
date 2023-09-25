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


import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;
import org.jooq.Query;

import java.util.ArrayList;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;
import static com.io7m.northpike.database.postgres.internal.Tables.WORK_ITEMS;
import static com.io7m.northpike.database.postgres.internal.Tables.WORK_ITEM_LOGS;

/**
 * Delete an assignment execution.
 */

public final class NPDBQAssignmentExecutionDelete
  extends NPDBQAbstract<UUID, NPDatabaseUnit>
  implements NPDatabaseQueriesAssignmentsType.ExecutionDeleteType
{
  private static final Service<UUID, NPDatabaseUnit, ExecutionDeleteType> SERVICE =
    new Service<>(
      ExecutionDeleteType.class,
      NPDBQAssignmentExecutionDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionDelete(
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
    final UUID execution)
  {
    final var batch = new ArrayList<Query>();

    final var executionWorkItems =
      context.select(WORK_ITEMS.WI_ID)
        .from(WORK_ITEMS)
        .where(WORK_ITEMS.WI_EXECUTION.eq(execution));

    /*
     * Delete the log associated with each work item, associated with this
     * assignment execution.
     */

    batch.add(
      context.deleteFrom(WORK_ITEM_LOGS)
        .where(WORK_ITEM_LOGS.WIL_ITEM.in(executionWorkItems))
    );

    /*
     * Delete each work item associated with this assignment execution.
     */

    batch.add(
      context.deleteFrom(WORK_ITEMS)
        .where(WORK_ITEMS.WI_EXECUTION.eq(execution))
    );

    /*
     * Delete the logs directly associated with the assignment execution.
     */

    batch.add(
      context.deleteFrom(ASSIGNMENT_EXECUTION_LOGS)
        .where(ASSIGNMENT_EXECUTION_LOGS.AEL_ID.eq(execution))
    );

    /*
     * Delete the assignment execution.
     */

    batch.add(
      context.deleteFrom(ASSIGNMENT_EXECUTIONS)
        .where(ASSIGNMENT_EXECUTIONS.AE_ID.eq(execution))
    );

    context.batch(batch).execute();
    return NPDatabaseUnit.UNIT;
  }
}
