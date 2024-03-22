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
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPPlansPagedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.model.plans.NPPlanSearchParameters;
import com.io7m.northpike.model.plans.NPPlanSummary;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLAN_TOOL_EXECUTIONS_SEARCH;
import static com.io7m.northpike.database.postgres.internal.Tables.TOOL_EXECUTION_DESCRIPTIONS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Search for plans.
 */

public final class NPDBQPlanSearch
  extends NPDBQAbstract<NPPlanSearchParameters, NPPlansPagedType>
  implements NPDatabaseQueriesPlansType.PlanSearchType
{
  private static final Service<NPPlanSearchParameters, NPPlansPagedType, PlanSearchType> SERVICE =
    new Service<>(PlanSearchType.class, NPDBQPlanSearch::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPlanSearch(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPPlansPagedType onExecute(
    final DSLContext context,
    final NPPlanSearchParameters parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      PLANS.leftJoin(PLAN_TOOL_EXECUTIONS_SEARCH)
        .on(PLANS.P_ID.eq(PLAN_TOOL_EXECUTIONS_SEARCH.PTE_PLAN));

    final var nameCondition =
      NPDBComparisons.createFuzzyMatchQuery(
        parameters.name(),
        PLANS.P_NAME,
        "PLANS.P_NAME_SEARCH"
      );

    final var descCondition =
      NPDBComparisons.createFuzzyMatchQuery(
        parameters.description(),
        PLANS.P_DESCRIPTION,
        "PLANS.P_DESCRIPTION_SEARCH"
      );

    final NPComparisonSetType<Long> comparisonSet =
      parameters.toolExecutions()
        .map(x -> {
          return context.select(TOOL_EXECUTION_DESCRIPTIONS.TED_ID)
            .from(TOOL_EXECUTION_DESCRIPTIONS)
            .where(
              TOOL_EXECUTION_DESCRIPTIONS.TED_NAME
                .eq(x.name().toString())
                .and(TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION
                       .eq(Long.valueOf(x.version())))
            )
            .fetchOne(TOOL_EXECUTION_DESCRIPTIONS.TED_ID);
        });

    final var toolSetCondition =
      NPDBComparisons.createSetMatchQueryLong(
        comparisonSet,
        PLAN_TOOL_EXECUTIONS_SEARCH.PTES_TOOLEXECS
      );

    final var allConditions =
      DSL.and(nameCondition, descCondition, toolSetCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(tableSource)
        .addSortField(new JQField(PLANS.P_NAME, JQOrder.ASCENDING))
        .addSortField(new JQField(PLANS.P_VERSION, JQOrder.ASCENDING))
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPPlanList(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  static final class NPPlanList
    extends NPAbstractSearch<NPPlanSummary>
    implements NPPlansPagedType
  {
    NPPlanList(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPPlanSummary> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPPlanList.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            PLANS.P_NAME,
            PLANS.P_VERSION,
            PLANS.P_DESCRIPTION
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPPlanSummary(
              new NPPlanIdentifier(
                NPPlanName.of(record.get(PLANS.P_NAME)),
                record.get(PLANS.P_VERSION).longValue()
              ),
              record.get(PLANS.P_DESCRIPTION)
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
