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
import com.io7m.northpike.database.api.NPAgentPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.ListType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.model.NPAgentSearchParameters;
import com.io7m.northpike.model.NPAgentSummary;
import com.io7m.northpike.model.NPPage;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_SEARCH;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Retrieve an agent.
 */

public final class NPDBQAgentSearch
  extends NPDBQAbstract<NPAgentSearchParameters, NPAgentPagedType>
  implements ListType
{
  private static final Service<NPAgentSearchParameters, NPAgentPagedType, ListType> SERVICE =
    new Service<>(ListType.class, NPDBQAgentSearch::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentSearch(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPAgentPagedType onExecute(
    final DSLContext context,
    final NPAgentSearchParameters parameters)
    throws NPDatabaseException
  {
    final var labelCondition =
      NPDBComparisons.createSetMatchQuery(
        parameters.matchLabels().map(NPAgentLabelName::toString),
        AGENT_LABEL_SEARCH.ALS_LABELS
      );

    final var deletedCondition =
      DSL.condition(AGENT_LABEL_SEARCH.A_DELETED.eq(Boolean.FALSE));

    final var allConditions =
      DSL.and(labelCondition, deletedCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(AGENT_LABEL_SEARCH)
        .addSortField(new JQField(AGENT_LABEL_SEARCH.A_NAME, JQOrder.ASCENDING))
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPAgentSearch(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  private static final class NPAgentSearch
    extends NPAbstractSearch<NPAgentSummary>
    implements NPAgentPagedType
  {
    NPAgentSearch(
      final List<JQKeysetRandomAccessPageDefinition> inPages)
    {
      super(inPages);
    }

    @Override
    protected NPPage<NPAgentSummary> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPAgentSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            AGENT_LABEL_SEARCH.A_NAME,
            AGENT_LABEL_SEARCH.A_ID
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPAgentSummary(
              new NPAgentID(record.get(AGENT_LABEL_SEARCH.A_ID)),
              record.get(AGENT_LABEL_SEARCH.A_NAME)
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
