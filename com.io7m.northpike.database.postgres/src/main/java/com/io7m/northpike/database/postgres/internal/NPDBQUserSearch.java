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
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType.SearchType;
import com.io7m.northpike.database.api.NPUsersPagedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.NPUserSearchParameters;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.USERS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * List users.
 */

public final class NPDBQUserSearch
  extends NPDBQAbstract<NPUserSearchParameters, NPUsersPagedType>
  implements SearchType
{
  private static final Service<NPUserSearchParameters, NPUsersPagedType, SearchType> SERVICE =
    new Service<>(SearchType.class, NPDBQUserSearch::new);

  /**
   * List users.
   *
   * @param transaction The transaction
   */

  public NPDBQUserSearch(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPUsersPagedType onExecute(
    final DSLContext context,
    final NPUserSearchParameters parameters)
    throws NPDatabaseException
  {
    final var nameCondition =
      NPDBComparisons.createFuzzyMatchQuery(
        parameters.name(),
        USERS.U_NAME,
        "USERS.U_NAME_SEARCH"
      );

    final var rolesCondition =
      NPDBComparisons.createSetMatchQuery(
        parameters.roles().map(roleName -> roleName.value().value()),
        USERS.U_ROLES
      );

    final var allCondition =
      DSL.and(nameCondition, rolesCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(USERS)
        .addSortField(new JQField(USERS.U_NAME, JQOrder.ASCENDING))
        .addWhereCondition(allCondition)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPDBQUserSearch.NPUserSearch(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  static final class NPUserSearch
    extends NPAbstractSearch<NPUser>
    implements NPUsersPagedType
  {
    NPUserSearch(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPUser> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPUserSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            USERS.U_NAME,
            USERS.U_ID,
            USERS.U_ROLES
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(NPDBQUserGet::mapUser);

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
