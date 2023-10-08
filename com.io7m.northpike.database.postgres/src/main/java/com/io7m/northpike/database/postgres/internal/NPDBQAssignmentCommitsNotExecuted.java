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
import com.io7m.jqpage.core.JQSelectDistinct;
import com.io7m.northpike.database.api.NPCommitSummaryPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.CommitsNotExecutedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryID;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.jqpage.core.JQOrder.ASCENDING;
import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTIONS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Retrieve commits that have not been executed.
 */

public final class NPDBQAssignmentCommitsNotExecuted
  extends NPDBQAbstract<CommitsNotExecutedType.Parameters, NPCommitSummaryPagedType>
  implements CommitsNotExecutedType
{
  private static final Service<Parameters, NPCommitSummaryPagedType, CommitsNotExecutedType> SERVICE =
    new Service<>(
      CommitsNotExecutedType.class,
      NPDBQAssignmentCommitsNotExecuted::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentCommitsNotExecuted(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPCommitSummaryPagedType onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      REPOSITORY_COMMITS
        .leftAntiJoin(ASSIGNMENT_EXECUTIONS)
        .on(REPOSITORY_COMMITS.RC_ID.eq(ASSIGNMENT_EXECUTIONS.AE_COMMIT));

    final var repositoryCondition =
      REPOSITORY_COMMITS.RC_REPOSITORY.eq(
        context.select(ASSIGNMENTS.A_REPOSITORY)
          .from(ASSIGNMENTS)
          .where(ASSIGNMENTS.A_NAME.eq(parameters.assignment().toString()))
      );

    final var timeRange = parameters.timeRange();
    final var timeConditionGe =
      REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED.ge(timeRange.lower());
    final var timeConditionLe =
      REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED.le(timeRange.upper());

    final var allConditions =
      DSL.and(
        repositoryCondition,
        timeConditionGe,
        timeConditionLe
      );

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(tableSource)
        .addSortField(new JQField(
          REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED,
          ASCENDING))
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPDBQAssignmentCommitsNotExecuted.NPCommitsNotExecuted(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  static final class NPCommitsNotExecuted
    extends NPAbstractSearch<NPCommitSummary>
    implements NPCommitSummaryPagedType
  {
    NPCommitsNotExecuted(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPCommitSummary> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPCommitsNotExecuted.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            REPOSITORY_COMMITS.RC_REPOSITORY,
            REPOSITORY_COMMITS.RC_COMMIT_ID,
            REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED,
            REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED,
            REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPCommitSummary(
              new NPCommitID(
                new NPRepositoryID(
                  record.get(REPOSITORY_COMMITS.RC_REPOSITORY)),
                new NPCommitUnqualifiedID(
                  record.get(REPOSITORY_COMMITS.RC_COMMIT_ID))
              ),
              record.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED),
              record.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED),
              record.get(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT)
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
