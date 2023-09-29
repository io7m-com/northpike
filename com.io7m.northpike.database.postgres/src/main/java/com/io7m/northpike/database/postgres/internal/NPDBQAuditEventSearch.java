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
import com.io7m.northpike.database.api.NPAuditPagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAuditType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPAuditSearchParameters;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPPage;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.DataType;
import org.jooq.Field;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;
import org.jooq.impl.SQLDataType;
import org.jooq.postgres.extensions.bindings.HstoreBinding;
import org.jooq.postgres.extensions.types.Hstore;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDBComparisons.createExactMatchQuery;
import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.tables.Audit.AUDIT;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Retrieve audit events.
 */

public final class NPDBQAuditEventSearch
  extends NPDBQAbstract<NPAuditSearchParameters, NPAuditPagedType>
  implements NPDatabaseQueriesAuditType.EventSearchType
{
  private static final Service<NPAuditSearchParameters, NPAuditPagedType, EventSearchType> SERVICE =
    new Service<>(EventSearchType.class, NPDBQAuditEventSearch::new);

  private static final DataType<Hstore> AU_DATA_TYPE =
    SQLDataType.OTHER.asConvertedDataType(new HstoreBinding());

  static final Field<Hstore> AU_DATA =
    DSL.field("AU_DATA", AU_DATA_TYPE);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAuditEventSearch(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPAuditPagedType onExecute(
    final DSLContext context,
    final NPAuditSearchParameters parameters)
    throws NPDatabaseException
  {
    final var conditionUser =
      parameters.owner()
        .map(userOrAgent -> {
          if (userOrAgent instanceof final NPAuditUserOrAgentType.User user) {
            return AUDIT.AU_USER.eq(user.id());
          }
          if (userOrAgent instanceof final NPAuditUserOrAgentType.Agent agent) {
            return AUDIT.AU_AGENT.eq(agent.id().value());
          }
          throw new IllegalStateException();
        })
        .orElse(DSL.trueCondition());

    final var conditionType =
      createExactMatchQuery(parameters.type(), AUDIT.AU_TYPE);

    final var conditionTime =
      AUDIT.AU_TIME.ge(parameters.timeRange().lower())
        .and(AUDIT.AU_TIME.le(parameters.timeRange().upper()));

    final var conditions =
      DSL.and(conditionUser, conditionType, conditionTime);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(AUDIT)
        .addSortField(new JQField(AUDIT.AU_TIME, JQOrder.ASCENDING))
        .addWhereCondition(conditions)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPAuditSearch(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  private static final class NPAuditSearch
    extends NPAbstractSearch<NPAuditEvent>
    implements NPAuditPagedType
  {
    NPAuditSearch(
      final List<JQKeysetRandomAccessPageDefinition> inPages)
    {
      super(inPages);
    }

    @Override
    protected NPPage<NPAuditEvent> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPAuditSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            AUDIT.AU_TIME,
            AUDIT.AU_TYPE,
            AUDIT.AU_USER,
            AUDIT.AU_AGENT,
            AU_DATA
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            final var userId =
              record.get(AUDIT.AU_USER);
            final var agentId =
              record.get(AUDIT.AU_AGENT);

            final NPAuditUserOrAgentType owner;
            if (userId != null) {
              owner = new NPAuditUserOrAgentType.User(userId);
            } else {
              owner = new NPAuditUserOrAgentType.Agent(new NPAgentID(agentId));
            }

            return new NPAuditEvent(
              record.get(AUDIT.AU_TIME),
              owner,
              record.get(AUDIT.AU_TYPE),
              record.get(AU_DATA).data()
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
