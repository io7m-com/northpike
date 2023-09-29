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
import com.io7m.northpike.database.api.NPCommitSummaryLinkedPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.database.postgres.internal.tables.RepositoryCommits;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitLink;
import com.io7m.northpike.model.NPCommitSearchParameters;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPCommitSummaryLinked;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryID;
import org.jooq.Condition;
import org.jooq.DSLContext;
import org.jooq.Name;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;
import java.util.Optional;

import static com.io7m.jqpage.core.JQOrder.ASCENDING;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORIES;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_LINKS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * List commits in the repository.
 */

public final class NPDBQRepositoryCommitsGet
  extends NPDBQAbstract<NPCommitSearchParameters, NPCommitSummaryLinkedPagedType>
  implements CommitsGetType
{
  private static final Service<NPCommitSearchParameters, NPCommitSummaryLinkedPagedType, CommitsGetType> SERVICE =
    new Service<>(CommitsGetType.class, NPDBQRepositoryCommitsGet::new);

  private static final JQField COMMIT_TIME_SORT =
    new JQField(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED, ASCENDING);

  private static final Name COMMITS_NEXT_NAME =
    DSL.name("commit_next");

  private static final RepositoryCommits COMMITS_NEXT =
    REPOSITORY_COMMITS.as(COMMITS_NEXT_NAME);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryCommitsGet(
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
  protected NPCommitSummaryLinkedPagedType onExecute(
    final DSLContext context,
    final NPCommitSearchParameters description)
    throws NPDatabaseException
  {
    final var source =
      REPOSITORY_COMMITS
        .leftOuterJoin(REPOSITORY_COMMIT_LINKS)
        .on(REPOSITORY_COMMITS.RC_ID.eq(REPOSITORY_COMMIT_LINKS.RCL_COMMIT))
        .leftOuterJoin(COMMITS_NEXT)
        .on(COMMITS_NEXT.RC_ID.eq(REPOSITORY_COMMIT_LINKS.RCL_COMMIT_NEXT));

    final var timeRangeCreated =
      description.timeRangeCreated();
    final var timeConditionCreatedLow =
      REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED.ge(timeRangeCreated.lower());
    final var timeConditionCreatedHigh =
      REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED.le(timeRangeCreated.upper());

    final var timeRangeReceived =
      description.timeRangeReceived();
    final var timeConditionReceivedLow =
      REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED.ge(timeRangeReceived.lower());
    final var timeConditionReceivedHigh =
      REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED.le(timeRangeReceived.upper());

    final var timeConditionCreatedSince =
      description.sinceCreated()
        .map(sinceValue -> {
          final var timeSelect =
            context.select(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED)
              .from(REPOSITORY_COMMITS)
              .join(REPOSITORIES)
              .on(REPOSITORIES.R_ID.eq(REPOSITORY_COMMITS.RC_REPOSITORY))
              .where(
                REPOSITORIES.R_ID.eq(sinceValue.repository().value())
                  .and(REPOSITORY_COMMITS.RC_COMMIT_ID
                         .eq(sinceValue.commitId().value()))
              ).limit(Integer.valueOf(1));
          return REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED.ge(timeSelect);
        })
        .orElseGet(DSL::trueCondition);

    final var timeConditionReceivedSince =
      description.sinceReceived()
        .map(sinceValue -> {
          final var timeSelect =
            context.select(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED)
              .from(REPOSITORY_COMMITS)
              .join(REPOSITORIES)
              .on(REPOSITORIES.R_ID.eq(REPOSITORY_COMMITS.RC_REPOSITORY))
              .where(
                REPOSITORIES.R_ID.eq(sinceValue.repository().value())
                  .and(REPOSITORY_COMMITS.RC_COMMIT_ID
                         .eq(sinceValue.commitId().value()))
              ).limit(Integer.valueOf(1));
          return REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED.ge(timeSelect);
        })
        .orElseGet(DSL::trueCondition);

    final var repositoryCondition =
      description.repository()
        .map(NPRepositoryID::value)
        .map(REPOSITORY_COMMITS.RC_REPOSITORY::eq)
        .orElseGet(DSL::trueCondition);

    final Condition conditions =
      DSL.and(
        timeConditionCreatedLow,
        timeConditionCreatedHigh,
        timeConditionReceivedLow,
        timeConditionReceivedHigh,
        timeConditionCreatedSince,
        timeConditionReceivedSince,
        repositoryCondition
      );

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context,
        JQKeysetRandomAccessPaginationParameters.forTable(source)
          .setPageSize(description.pageSize())
          .addSortField(COMMIT_TIME_SORT)
          .addWhereCondition(conditions)
          .setStatementListener(statement -> {
            this.transactionSpan()
              .setAttribute(DB_STATEMENT, statement.toString());
          })
          .build()
      );

    return new NPCommitsSearch(pages);
  }

  private static final class NPCommitsSearch
    extends NPAbstractSearch<NPCommitSummaryLinked>
    implements NPCommitSummaryLinkedPagedType
  {
    NPCommitsSearch(
      final List<JQKeysetRandomAccessPageDefinition> inPages)
    {
      super(inPages);
    }

    @Override
    protected NPPage<NPCommitSummaryLinked> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPCommitsSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            REPOSITORY_COMMITS.RC_COMMIT_ID,
            REPOSITORY_COMMITS.RC_REPOSITORY,
            REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED,
            REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED,
            REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT,
            COMMITS_NEXT.RC_COMMIT_ID,
            COMMITS_NEXT.RC_REPOSITORY
          ));

        recordQuery(query);

        final var items =
          query.fetch().map(record -> {
            final var commit =
              new NPCommitID(
                new NPRepositoryID(record.get(REPOSITORY_COMMITS.RC_REPOSITORY)),
                new NPCommitUnqualifiedID(record.get(REPOSITORY_COMMITS.RC_COMMIT_ID))
              );

            final var nextRepos =
              record.get(COMMITS_NEXT.RC_REPOSITORY);
            final var nextCommit =
              Optional.ofNullable(record.get(COMMITS_NEXT.RC_COMMIT_ID))
                .map(NPCommitUnqualifiedID::new)
                .orElse(null);

            return new NPCommitSummaryLinked(
              new NPCommitSummary(
                commit,
                record.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED),
                record.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED),
                record.get(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT)
              ),
              new NPCommitLink(
                commit,
                Optional.ofNullable(nextRepos)
                  .map(u -> {
                    return new NPCommitID(
                      new NPRepositoryID(nextRepos),
                      nextCommit
                    );
                  })
              )
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
        throw NPDatabaseExceptions.handleDatabaseException(transaction, e);
      } finally {
        querySpan.end();
      }
    }
  }
}
