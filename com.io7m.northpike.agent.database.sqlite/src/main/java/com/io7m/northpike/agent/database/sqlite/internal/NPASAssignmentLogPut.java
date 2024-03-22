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
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPWorkItemLogRecordOnAgent;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import org.jooq.DSLContext;
import org.jooq.Record1;
import org.jooq.Select;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.agent.database.sqlite.internal.Tables.AGENTS;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;

/**
 * Log work execution output.
 */

public final class NPASAssignmentLogPut
  extends NPASQAbstract<NPWorkItemLogRecordOnAgent, NPAgentDatabaseUnit>
  implements AssignmentLogPutType
{
  private static final Service<
    NPWorkItemLogRecordOnAgent, NPAgentDatabaseUnit, AssignmentLogPutType> SERVICE =
    new Service<>(AssignmentLogPutType.class, NPASAssignmentLogPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAssignmentLogPut(
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

  private static byte[] serializeAttributes(
    final Map<String, String> attributes)
    throws NPAgentDatabaseException
  {
    try {
      final var properties = new Properties();
      for (final var entry : attributes.entrySet()) {
        properties.setProperty(entry.getKey(), entry.getValue());
      }
      final var output = new ByteArrayOutputStream();
      properties.storeToXML(output, "", StandardCharsets.UTF_8);
      return output.toByteArray();
    } catch (final IOException e) {
      throw new NPAgentDatabaseException(
        Objects.requireNonNullElse(e.getMessage(), "I/O error."),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  @Override
  protected NPAgentDatabaseUnit onExecute(
    final DSLContext context,
    final NPWorkItemLogRecordOnAgent input)
    throws NPAgentDatabaseException
  {
    final var logRecord =
      input.logRecord();
    final var identifier =
      logRecord.workItem();

    final var query =
      context.insertInto(ASSIGNMENT_EXECUTION_LOGS)
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_AGENT,
          findAgent(context, input.agent())
        )
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_ASSIGNMENT,
          identifier.assignmentExecutionId().toString())
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_TASK,
          identifier.planElementName().toString())
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_TIME,
          logRecord.timestamp().toString())
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX,
          Long.valueOf(logRecord.eventIndex()))
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE,
          logRecord.type())
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE,
          logRecord.message())
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_ATTRIBUTES,
          serializeAttributes(logRecord.attributes()))
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_FORMAT,
          "CEDARBRIDGE")
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_VERSION,
          Integer.valueOf(1))
        .set(
          ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_DATA,
          NPASStoredExceptions.serializeExceptionOptional(logRecord.exception())
        );

    recordQuery(query);

    query.execute();
    return NPAgentDatabaseUnit.UNIT;
  }

  private static Select<Record1<Integer>> findAgent(
    final DSLContext context,
    final NPAgentLocalName agent)
  {
    return context.select(AGENTS.A_ID)
      .from(AGENTS)
      .where(AGENTS.A_NAME.eq(agent.toString()));
  }
}
