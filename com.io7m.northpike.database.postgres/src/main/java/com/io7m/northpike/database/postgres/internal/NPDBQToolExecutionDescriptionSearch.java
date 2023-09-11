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
import com.io7m.jqpage.core.JQSelectDistinct;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.database.api.NPToolExecutionDescriptionsPagedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.TOOL_EXECUTION_DESCRIPTIONS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Search for tool execution descriptions.
 */

public final class NPDBQToolExecutionDescriptionSearch
  extends NPDBQAbstract<NPToolExecutionDescriptionSearchParameters, NPToolExecutionDescriptionsPagedType>
  implements NPDatabaseQueriesToolsType.SearchExecutionDescriptionType
{
  private static final Service<
    NPToolExecutionDescriptionSearchParameters,
    NPToolExecutionDescriptionsPagedType,
    SearchExecutionDescriptionType
    > SERVICE =
    new Service<>(
      SearchExecutionDescriptionType.class,
      NPDBQToolExecutionDescriptionSearch::new
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQToolExecutionDescriptionSearch(
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
  protected NPToolExecutionDescriptionsPagedType onExecute(
    final DSLContext context,
    final NPToolExecutionDescriptionSearchParameters parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      TOOL_EXECUTION_DESCRIPTIONS;

    final var sortName =
      new JQField(TOOL_EXECUTION_DESCRIPTIONS.TED_NAME, JQOrder.ASCENDING);
    final var sortVersion =
      new JQField(TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION, JQOrder.ASCENDING);

    final var toolCondition =
      parameters.forTool()
        .map(t -> {
          return TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME.eq(t.value().value());
        })
        .orElse(DSL.trueCondition());

    final var allConditions =
      DSL.and(toolCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(tableSource)
        .addSortField(sortName)
        .addSortField(sortVersion)
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPDBQToolExecutionDescriptionSearch.NPToolExecutionDescriptionSearch(
      pages);
  }

  static final class NPToolExecutionDescriptionSearch
    extends NPAbstractSearch<NPToolExecutionDescriptionSummary>
    implements NPToolExecutionDescriptionsPagedType
  {
    NPToolExecutionDescriptionSearch(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPToolExecutionDescriptionSummary> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPToolExecutionDescriptionSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            TOOL_EXECUTION_DESCRIPTIONS.TED_NAME,
            TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION,
            TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME,
            TOOL_EXECUTION_DESCRIPTIONS.TED_DESCRIPTION
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPToolExecutionDescriptionSummary(
              new NPToolExecutionIdentifier(
                NPToolExecutionName.of(
                  record.get(TOOL_EXECUTION_DESCRIPTIONS.TED_NAME)
                ),
                record.<Long>get(
                  TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION
                ).longValue()
              ),
              NPToolName.of(
                record.get(TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME)
              ),
              record.get(TOOL_EXECUTION_DESCRIPTIONS.TED_DESCRIPTION)
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
