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
import com.io7m.northpike.database.postgres.internal.NPDBMatch.QuerySetType.QuerySetCondition;
import com.io7m.northpike.database.postgres.internal.NPDBMatch.QuerySetType.QuerySetIntersection;
import com.io7m.northpike.database.postgres.internal.NPDBMatch.QuerySetType.QuerySetUnion;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentListParameters;
import com.io7m.northpike.model.NPAgentSummary;
import com.io7m.northpike.model.NPPage;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.Field;
import org.jooq.Name;
import org.jooq.Record2;
import org.jooq.Select;
import org.jooq.Table;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;
import org.jooq.impl.SQLDataType;

import java.util.List;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABELS;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;
import static com.io7m.northpike.database.postgres.internal.tables.Agents.AGENTS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Retrieve an agent.
 */

public final class NPDBQAgentList
  extends NPDBQAbstract<NPAgentListParameters, NPAgentPagedType>
  implements ListType
{
  private static final Service<NPAgentListParameters, NPAgentPagedType, ListType> SERVICE =
    new Service<>(ListType.class, NPDBQAgentList::new);

  private static final Name AGENT_SEARCH =
    DSL.name("AGENT_SEARCH");

  private static final Field<String> AGENT_SEARCH_NAME_FIELD =
    DSL.field(
      DSL.name(AGENT_SEARCH, DSL.name("A_NAME")),
      SQLDataType.VARCHAR
    );

  private static final Field<UUID> AGENT_SEARCH_ID_FIELD =
    DSL.field(
      DSL.name(AGENT_SEARCH, DSL.name("A_ID")),
      SQLDataType.UUID
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentList(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPAgentPagedType onExecute(
    final DSLContext context,
    final NPAgentListParameters parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      AGENTS
        .leftOuterJoin(AGENT_LABELS)
        .on(AGENTS.A_ID.eq(AGENT_LABELS.AL_AGENT))
        .join(AGENT_LABEL_DEFINITIONS)
        .on(AGENT_LABELS.AL_LABEL.eq(AGENT_LABEL_DEFINITIONS.ALD_ID));

    final var querySet =
      NPDBMatch.ofAgentLabelMatch(parameters.matchLabels());
    final var query =
      generateQuerySetFor(context, tableSource, querySet)
        .asTable(AGENT_SEARCH);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(query)
        .addSortField(new JQField(AGENT_SEARCH_NAME_FIELD, JQOrder.ASCENDING))
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

  private static Select<Record2<UUID, String>> generateQuerySetFor(
    final DSLContext context,
    final Table<?> tableSource,
    final NPDBMatch.QuerySetType querySet)
  {
    if (querySet instanceof final QuerySetCondition c) {
      return context.select(AGENTS.A_ID, AGENTS.A_NAME)
        .from(tableSource)
        .where(c.condition());
    }

    if (querySet instanceof final QuerySetUnion u) {
      final var rq0 = generateQuerySetFor(context, tableSource, u.q0());
      final var rq1 = generateQuerySetFor(context, tableSource, u.q1());
      return rq0.union(rq1);
    }

    if (querySet instanceof final QuerySetIntersection u) {
      final var rq0 = generateQuerySetFor(context, tableSource, u.q0());
      final var rq1 = generateQuerySetFor(context, tableSource, u.q1());
      return rq0.intersect(rq1);
    }

    throw new IllegalStateException();
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
            AGENT_SEARCH_ID_FIELD,
            AGENT_SEARCH_NAME_FIELD
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPAgentSummary(
              new NPAgentID(record.get(AGENT_SEARCH_ID_FIELD)),
              record.get(AGENT_SEARCH_NAME_FIELD)
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
