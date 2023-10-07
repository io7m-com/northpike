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
import com.io7m.northpike.database.api.NPAssignmentsPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDBQAssignmentGet.mapSchedule;
import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Search for tool execution descriptions.
 */

public final class NPDBQAssignmentSearch
  extends NPDBQAbstract<NPAssignmentSearchParameters, NPAssignmentsPagedType>
  implements NPDatabaseQueriesAssignmentsType.SearchType
{
  private static final Service<
    NPAssignmentSearchParameters,
    NPAssignmentsPagedType,
    SearchType
    > SERVICE =
    new Service<>(
      SearchType.class,
      NPDBQAssignmentSearch::new
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentSearch(
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
  protected NPAssignmentsPagedType onExecute(
    final DSLContext context,
    final NPAssignmentSearchParameters parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      ASSIGNMENTS
        .join(PLANS)
        .on(ASSIGNMENTS.A_PLAN.eq(PLANS.P_ID));

    final var sortName =
      new JQField(ASSIGNMENTS.A_NAME, JQOrder.ASCENDING);

    final var reposCondition =
      parameters.repositoryId()
        .map(NPRepositoryID::value)
        .map(ASSIGNMENTS.A_REPOSITORY::eq)
        .orElse(DSL.trueCondition());

    final var planCondition =
      parameters.plan()
        .map(id -> {
          return DSL.and(
            ASSIGNMENTS.A_PLAN.eq(
              context.select(PLANS.P_ID)
                .from(PLANS)
                .where(
                  PLANS.P_NAME.eq(id.name().name().value())
                    .and(PLANS.P_VERSION.eq(Long.valueOf(id.version())))
                )
            )
          );
        })
        .orElse(DSL.trueCondition());

    final var nameCondition =
      NPDBComparisons.createFuzzyMatchQuery(
        parameters.nameQuery(),
        ASSIGNMENTS.A_NAME,
        "ASSIGNMENTS.A_NAME_SEARCH"
      );

    final var allConditions =
      DSL.and(reposCondition, planCondition, nameCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(tableSource)
        .addSortField(sortName)
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPDBQAssignmentSearch.NPAssignmentSearch(pages);
  }

  static final class NPAssignmentSearch
    extends NPAbstractSearch<NPAssignment>
    implements NPAssignmentsPagedType
  {
    NPAssignmentSearch(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPAssignment> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPAssignmentSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            ASSIGNMENTS.A_NAME,
            ASSIGNMENTS.A_REPOSITORY,
            ASSIGNMENTS.A_SCHEDULE,
            ASSIGNMENTS.A_SCHEDULE_CUTOFF,
            PLANS.P_NAME,
            PLANS.P_VERSION
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPAssignment(
              NPAssignmentName.of(record.get(ASSIGNMENTS.A_NAME)),
              new NPRepositoryID(record.get(ASSIGNMENTS.A_REPOSITORY)),
              new NPPlanIdentifier(
                NPPlanName.of(record.get(PLANS.P_NAME)),
                record.<Long>get(PLANS.P_VERSION).longValue()
              ),
              mapSchedule(record)
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
