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
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAssignmentLogsType.AssignmentLogGetType.Parameters;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemLogRecord;
import com.io7m.northpike.model.NPWorkItemLogRecordOnAgent;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.agent.database.sqlite.internal.Tables.AGENTS;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;

/**
 * Log work execution output.
 */

public final class NPASAssignmentLogGet
  extends NPASQAbstract<Parameters, Optional<NPWorkItemLogRecordOnAgent>>
  implements AssignmentLogGetType
{
  private static final Service<
    Parameters, Optional<NPWorkItemLogRecordOnAgent>, AssignmentLogGetType> SERVICE =
    new Service<>(AssignmentLogGetType.class, NPASAssignmentLogGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAssignmentLogGet(
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

  static Optional<NPStoredException> deserializeExceptionOptional(
    final String format,
    final Integer formatVersion,
    final byte[] data)
    throws NPAgentDatabaseException
  {
    if (data == null) {
      return Optional.empty();
    }

    return switch (format) {
      case "CEDARBRIDGE" -> {
        yield Optional.of(deserializeExceptionOptionalCedarbridge(
          formatVersion,
          data));
      }

      default -> {
        throw new NPAgentDatabaseException(
          "Unsupported exception serialization format.",
          NPStandardErrorCodes.errorIo(),
          Map.ofEntries(
            Map.entry("Format", "CEDARBRIDGE")
          ),
          Optional.empty()
        );
      }
    };
  }

  static NPStoredException deserializeExceptionOptionalCedarbridge(
    final Integer formatVersion,
    final byte[] data)
    throws NPAgentDatabaseException
  {
    return switch (formatVersion.intValue()) {
      case 1 -> {
        yield deserializeExceptionOptionalCedarbridge1(data);
      }

      default -> {
        throw new NPAgentDatabaseException(
          "Unsupported exception serialization format.",
          NPStandardErrorCodes.errorIo(),
          Map.ofEntries(
            Map.entry("Format", "CEDARBRIDGE"),
            Map.entry("FormatVersion", formatVersion.toString())
          ),
          Optional.empty()
        );
      }
    };
  }

  static NPStoredException deserializeExceptionOptionalCedarbridge1(
    final byte[] data)
  {
    return NPASStoredExceptions.deserializeException(data);
  }

  static Map<String, String> deserializeAttributes(
    final byte[] bytes)
    throws NPAgentDatabaseException
  {
    try (var input = new ByteArrayInputStream(bytes)) {
      final var properties = new Properties();
      properties.loadFromXML(input);

      final var r = new HashMap<String, String>();
      for (final var name : properties.stringPropertyNames()) {
        final var value = properties.getProperty(name);
        r.put(name, value);
      }
      return Map.copyOf(r);
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
  protected Optional<NPWorkItemLogRecordOnAgent> onExecute(
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

    final var tableSource =
      ASSIGNMENT_EXECUTION_LOGS
        .join(AGENTS)
        .on(AGENTS.A_ID.eq(ASSIGNMENT_EXECUTION_LOGS.AEL_AGENT));

    final var query =
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
          ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_TASK,
          AGENTS.A_NAME
        ).from(tableSource)
        .where(whereCondition);

    recordQuery(query);

    final var result = query.fetchOptional();
    if (result.isEmpty()) {
      return Optional.empty();
    }

    final var rec = result.get();
    return Optional.of(
      new NPWorkItemLogRecordOnAgent(
        NPAgentLocalName.of(rec.get(AGENTS.A_NAME)),
        new NPWorkItemLogRecord(
          new NPWorkItemIdentifier(
            NPAssignmentExecutionID.of(
              rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_ASSIGNMENT)
            ),
            new RDottedName(
              rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_WORK_ITEM_TASK)
            )
          ),
          OffsetDateTime.parse(rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_TIME)),
          rec.<Long>get(ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX).longValue(),
          rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE),
          deserializeAttributes(rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_ATTRIBUTES)),
          rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE),
          deserializeExceptionOptional(
            rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_FORMAT),
            rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_VERSION),
            rec.get(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_DATA)
          )
        )
      )
    );
  }
}
