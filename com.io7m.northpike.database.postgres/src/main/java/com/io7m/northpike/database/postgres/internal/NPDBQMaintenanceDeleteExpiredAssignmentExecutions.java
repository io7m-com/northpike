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

import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredAssignmentExecutionsType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import org.jooq.DSLContext;
import org.jooq.Query;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.Arrays;

import static com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionDeleteType.DeletionScope.DELETE_LOGS;
import static com.io7m.northpike.database.postgres.internal.NPDBQAssignmentExecutionDelete.deletionStatements;
import static com.io7m.northpike.database.postgres.internal.tables.AssignmentExecutions.ASSIGNMENT_EXECUTIONS;

/**
 * A query to run maintenance.
 */

public final class NPDBQMaintenanceDeleteExpiredAssignmentExecutions
  extends NPDBQAbstract<OffsetDateTime, Long>
  implements DeleteExpiredAssignmentExecutionsType
{
  private static final Service<OffsetDateTime, Long, DeleteExpiredAssignmentExecutionsType> SERVICE =
    new Service<>(
      DeleteExpiredAssignmentExecutionsType.class,
      NPDBQMaintenanceDeleteExpiredAssignmentExecutions::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQMaintenanceDeleteExpiredAssignmentExecutions(
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
  protected Long onExecute(
    final DSLContext context,
    final OffsetDateTime parameters)
  {
    final var oldIds =
      context.select(ASSIGNMENT_EXECUTIONS.AE_ID)
        .from(ASSIGNMENT_EXECUTIONS)
        .where(ASSIGNMENT_EXECUTIONS.AE_CREATED.lt(parameters))
        .fetch();

    final var batch = new ArrayList<Query>();
    for (final var id : oldIds) {
      deletionStatements(
        context,
        new NPAssignmentExecutionID(id.get(ASSIGNMENT_EXECUTIONS.AE_ID)),
        DELETE_LOGS,
        batch
      );
    }

    return Long.valueOf(
      Arrays.stream(context.batch(batch).execute())
        .mapToLong(x -> (long) x)
        .sum()
    );
  }
}
