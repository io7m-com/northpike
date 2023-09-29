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
import com.io7m.northpike.database.api.NPAssignmentExecutionsPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionSearchParameters;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateKind;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import io.opentelemetry.api.trace.Span;
import org.jooq.Condition;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CANCELLED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_CREATED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_FAILED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_REQUESTED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_RUNNING;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentExecutionStatusT.ASSIGNMENT_EXECUTION_SUCCEEDED;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Search for tool execution descriptions.
 */

public final class NPDBQAssignmentExecutionsSearch
  extends NPDBQAbstract<NPAssignmentExecutionSearchParameters, NPAssignmentExecutionsPagedType>
  implements NPDatabaseQueriesAssignmentsType.ExecutionSearchType
{
  private static final Service<
    NPAssignmentExecutionSearchParameters,
    NPAssignmentExecutionsPagedType,
    ExecutionSearchType
    > SERVICE =
    new Service<>(
      ExecutionSearchType.class,
      NPDBQAssignmentExecutionsSearch::new
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionsSearch(
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
  protected NPAssignmentExecutionsPagedType onExecute(
    final DSLContext context,
    final NPAssignmentExecutionSearchParameters parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      ASSIGNMENT_EXECUTIONS
        .leftOuterJoin(ASSIGNMENTS)
        .on(ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT.eq(ASSIGNMENTS.A_ID))
        .leftOuterJoin(PLANS)
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

    final var stateCondition =
      createAssignmentStateQuery(parameters.state());

    final var nameCondition =
      NPDBComparisons.createFuzzyMatchQuery(
        parameters.nameQuery(),
        ASSIGNMENTS.A_NAME,
        "ASSIGNMENTS.A_NAME_SEARCH"
      );

    final var allConditions =
      DSL.and(reposCondition, planCondition, nameCondition, stateCondition);

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

    return new NPAssignmentExecutionSearch(pages);
  }

  private static Condition createAssignmentStateQuery(
    final NPComparisonExactType<NPAssignmentExecutionStateKind> state)
  {
    if (state instanceof final NPComparisonExactType.IsEqualTo<NPAssignmentExecutionStateKind> equalTo) {
      return ASSIGNMENT_EXECUTIONS.AE_STATUS.eq(toDBStatus(equalTo.value()));
    }
    if (state instanceof final NPComparisonExactType.IsNotEqualTo<NPAssignmentExecutionStateKind> notEqualTo) {
      return ASSIGNMENT_EXECUTIONS.AE_STATUS.ne(toDBStatus(notEqualTo.value()));
    }
    if (state instanceof NPComparisonExactType.Anything<NPAssignmentExecutionStateKind>) {
      return DSL.trueCondition();
    }
    throw new IllegalStateException("Unrecognized comparison: " + state);
  }

  private static AssignmentExecutionStatusT toDBStatus(
    final NPAssignmentExecutionStateKind s)
  {
    return switch (s) {
      case CANCELLED -> ASSIGNMENT_EXECUTION_CANCELLED;
      case CREATED -> ASSIGNMENT_EXECUTION_CREATED;
      case CREATION_FAILED -> ASSIGNMENT_EXECUTION_FAILED;
      case FAILED -> ASSIGNMENT_EXECUTION_FAILED;
      case REQUESTED -> ASSIGNMENT_EXECUTION_REQUESTED;
      case RUNNING -> ASSIGNMENT_EXECUTION_RUNNING;
      case SUCCEEDED -> ASSIGNMENT_EXECUTION_SUCCEEDED;
    };
  }

  static final class NPAssignmentExecutionSearch
    extends NPAbstractSearch<NPAssignmentExecutionStateType>
    implements NPAssignmentExecutionsPagedType
  {
    NPAssignmentExecutionSearch(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPAssignmentExecutionStateType> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPAssignmentExecutionSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            ASSIGNMENTS.A_NAME,
            ASSIGNMENTS.A_REPOSITORY,
            ASSIGNMENT_EXECUTIONS.AE_ASSIGNMENT_NAME,
            ASSIGNMENT_EXECUTIONS.AE_COMMIT_NAME,
            ASSIGNMENT_EXECUTIONS.AE_CREATED,
            ASSIGNMENT_EXECUTIONS.AE_ENDED,
            ASSIGNMENT_EXECUTIONS.AE_ID,
            ASSIGNMENT_EXECUTIONS.AE_STARTED,
            ASSIGNMENT_EXECUTIONS.AE_STATUS,
            PLANS.P_NAME,
            PLANS.P_VERSION
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch()
            .map(NPDBQAssignmentExecutionGet::mapAssignmentExecutionRecord);

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
