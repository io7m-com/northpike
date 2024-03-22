/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogDeleteType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogDeleteType.Parameters;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import static com.io7m.northpike.agent.database.sqlite.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;

/**
 * Log work execution output.
 */

public final class NPASAssignmentLogDelete
  extends NPASQAbstract<Parameters, NPAgentDatabaseUnit>
  implements AssignmentLogDeleteType
{
  private static final Service<Parameters, NPAgentDatabaseUnit, AssignmentLogDeleteType> SERVICE =
    new Service<>(AssignmentLogDeleteType.class, NPASAssignmentLogDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAssignmentLogDelete(
    final NPASTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPASQueryProviderType provider()
  {
    return () -> SERVICE;
  }


  @Override
  protected NPAgentDatabaseUnit onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPAgentDatabaseException
  {
    final var identifier = parameters.identifier();

    final var assignmentCondition =
      ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_ASSIGNMENT.eq(
        identifier.assignmentExecutionId().toString());
    final var taskCondition =
      ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_TASK.eq(
        identifier.planElementName().toString());
    final var indexCondition =
      ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX.eq(Long.valueOf(parameters.index()));
    final var whereCondition =
      DSL.and(assignmentCondition, taskCondition, indexCondition);

    final var query =
      context.deleteFrom(ASSIGNMENT_EXECUTION_LOGS)
        .where(whereCondition);

    recordQuery(query);
    query.execute();
    return NPAgentDatabaseUnit.UNIT;
  }
}
