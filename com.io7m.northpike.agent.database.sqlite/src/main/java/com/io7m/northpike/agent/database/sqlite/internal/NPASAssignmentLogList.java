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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogListType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogListType.Parameters;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemLogRecord;
import com.io7m.northpike.model.NPWorkItemLogRecordOnAgent;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import org.jooq.DSLContext;
import org.jooq.Record;

import java.time.OffsetDateTime;
import java.util.ArrayList;
import java.util.List;

import static com.io7m.northpike.agent.database.sqlite.internal.NPASAssignmentLogGet.deserializeAttributes;
import static com.io7m.northpike.agent.database.sqlite.internal.NPASAssignmentLogGet.deserializeExceptionOptional;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.AGENTS;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;

/**
 * Log work execution output.
 */

public final class NPASAssignmentLogList
  extends NPASQAbstract<Parameters, List<NPWorkItemLogRecordOnAgent>>
  implements AssignmentLogListType
{
  private static final Service<
    Parameters, List<NPWorkItemLogRecordOnAgent>, AssignmentLogListType> SERVICE =
    new Service<>(AssignmentLogListType.class, NPASAssignmentLogList::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAssignmentLogList(
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
  protected List<NPWorkItemLogRecordOnAgent> onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPAgentDatabaseException
  {
    final var whereCondition =
      ASSIGNMENT_EXECUTION_LOGS.AEL_AGENT.eq(
        context.select(AGENTS.A_ID)
          .from(AGENTS)
          .where(AGENTS.A_NAME.eq(parameters.agent().toString()))
      );

    final var results =
      context.select(
          ASSIGNMENT_EXECUTION_LOGS.AEL_ATTRIBUTES,
          ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_DATA,
          ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_FORMAT,
          ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_VERSION,
          ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX,
          ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE,
          ASSIGNMENT_EXECUTION_LOGS.AEL_TIME,
          ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE,
          ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_ASSIGNMENT,
          ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_TASK
        ).from(ASSIGNMENT_EXECUTION_LOGS)
        .where(whereCondition)
        .orderBy(
          ASSIGNMENT_EXECUTION_LOGS.AEL_TIME,
          ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX)
        .limit(Long.valueOf(parameters.limit()))
        .offset(Long.valueOf(parameters.offset()))
        .fetch();

    final var output = new ArrayList<NPWorkItemLogRecordOnAgent>();
    for (final var result : results) {
      output.add(mapRecord(parameters.agent(), result));
    }
    return List.copyOf(output);
  }

  private static NPWorkItemLogRecordOnAgent mapRecord(
    final NPAgentLocalName agent,
    final Record r)
    throws NPAgentDatabaseException
  {
    return new NPWorkItemLogRecordOnAgent(
      agent,
      new NPWorkItemLogRecord(
        new NPWorkItemIdentifier(
          NPAssignmentExecutionID.of(
            r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_ASSIGNMENT)
          ),
          new RDottedName(
            r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_TASK)
          )
        ),
        OffsetDateTime.parse(r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_TIME)),
        r.<Long>get(ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX).longValue(),
        r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE),
        deserializeAttributes(r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_ATTRIBUTES)),
        r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE),
        deserializeExceptionOptional(
          r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_FORMAT),
          r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_VERSION),
          r.get(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_DATA)
        )
      )
    );
  }
}
