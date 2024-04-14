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


import com.io7m.jqpage.core.JQField;
import com.io7m.jqpage.core.JQKeysetRandomAccessPageDefinition;
import com.io7m.jqpage.core.JQKeysetRandomAccessPagination;
import com.io7m.jqpage.core.JQKeysetRandomAccessPaginationParameters;
import com.io7m.jqpage.core.JQOrder;
import com.io7m.northpike.database.api.NPAssignmentExecutionLogPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionLogListType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionLogMessage;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;
import org.jooq.impl.SQLDataType;
import org.jooq.postgres.extensions.bindings.HstoreBinding;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Search execution logs.
 */

public final class NPDBQAssignmentExecutionLogList
  extends NPDBQAbstract<AssignmentExecutionLogListType.Parameters, NPAssignmentExecutionLogPagedType>
  implements AssignmentExecutionLogListType
{
  private static final Service<
    Parameters, NPAssignmentExecutionLogPagedType, AssignmentExecutionLogListType> SERVICE =
    new Service<>(
      AssignmentExecutionLogListType.class,
      NPDBQAssignmentExecutionLogList::new
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionLogList(
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
  protected NPAssignmentExecutionLogPagedType onExecute(
    final DSLContext context,
    final Parameters parameters)
  {
    final var sortTime =
      new JQField(
        ASSIGNMENT_EXECUTION_LOGS.AEL_TIME,
        parameters.timeAscending()
          ? JQOrder.ASCENDING
          : JQOrder.DESCENDING
      );

    final var executionCondition =
      ASSIGNMENT_EXECUTION_LOGS.AEL_ID.eq(
        parameters.execution().value());

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(ASSIGNMENT_EXECUTION_LOGS)
        .addSortField(sortTime)
        .addWhereCondition(executionCondition)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPAssignmentExecutionLogList(pages);
  }

  static final class NPAssignmentExecutionLogList
    extends NPAbstractSearch<NPAssignmentExecutionLogMessage>
    implements NPAssignmentExecutionLogPagedType
  {
    NPAssignmentExecutionLogList(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPAssignmentExecutionLogMessage> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPAssignmentExecutionLogList.page");

      try {
        final var attributesType =
          SQLDataType.OTHER.asConvertedDataType(new HstoreBinding());
        final var attributesField =
          DSL.field("AEL_ATTRIBUTES", attributesType);

        final var query =
          page.queryFields(context, List.of(
            ASSIGNMENT_EXECUTION_LOGS.AEL_ID,
            ASSIGNMENT_EXECUTION_LOGS.AEL_TIME,
            ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE,
            ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE,
            attributesField
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPAssignmentExecutionLogMessage(
              new NPAssignmentExecutionID(
                record.get(ASSIGNMENT_EXECUTION_LOGS.AEL_ID)
              ),
              record.get(ASSIGNMENT_EXECUTION_LOGS.AEL_TIME),
              record.get(ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE),
              record.get(ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE),
              record.get(attributesField).data()
            );
          });

        return new NPPage<>(
          items,
          (int) page.index(),
          this.pageCount(),
          page.firstOffset()
        );
      } catch (final DataAccessException e) {
        querySpan.recordException(e);
        throw handleDatabaseException(transaction, e);
      } finally {
        querySpan.end();
      }
    }
  }
}
