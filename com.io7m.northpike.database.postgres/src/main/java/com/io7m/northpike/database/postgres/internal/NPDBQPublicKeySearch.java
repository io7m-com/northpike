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
import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.database.api.NPPublicKeysPagedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPPublicKey;
import com.io7m.northpike.model.NPPublicKeySearchParameters;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.PUBLIC_KEYS;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * List public keys.
 */

public final class NPDBQPublicKeySearch
  extends NPDBQAbstract<NPPublicKeySearchParameters, NPPublicKeysPagedType>
  implements NPDatabaseQueriesPublicKeysType.SearchType
{
  private static final Service<NPPublicKeySearchParameters, NPPublicKeysPagedType, SearchType> SERVICE =
    new Service<>(SearchType.class, NPDBQPublicKeySearch::new);

  /**
   * List public keys.
   *
   * @param transaction The transaction
   */

  public NPDBQPublicKeySearch(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPPublicKeysPagedType onExecute(
    final DSLContext context,
    final NPPublicKeySearchParameters parameters)
    throws NPDatabaseException
  {
    final var userIdCondition =
      NPDBComparisons.createFuzzyMatchArrayQuery(
        parameters.userId(),
        PUBLIC_KEYS.PK_USER_IDS,
        "PUBLIC_KEYS.PK_USER_SEARCH"
      );

    final var allConditions =
      DSL.and(userIdCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(PUBLIC_KEYS)
        .addSortField(new JQField(PUBLIC_KEYS.PK_FINGERPRINT, JQOrder.ASCENDING))
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPDBQPublicKeySearch.NPPublicKeySearch(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  static final class NPPublicKeySearch
    extends NPAbstractSearch<NPPublicKey>
    implements NPPublicKeysPagedType
  {
    NPPublicKeySearch(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPPublicKey> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPPublicKeySearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            PUBLIC_KEYS.PK_ENCODED,
            PUBLIC_KEYS.PK_FINGERPRINT,
            PUBLIC_KEYS.PK_TIME_CREATED,
            PUBLIC_KEYS.PK_TIME_EXPIRES,
            PUBLIC_KEYS.PK_USER_IDS
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPPublicKey(
              Set.of(record.get(PUBLIC_KEYS.PK_USER_IDS)),
              new NPFingerprint(record.get(PUBLIC_KEYS.PK_FINGERPRINT)),
              record.get(PUBLIC_KEYS.PK_TIME_CREATED),
              Optional.ofNullable(record.get(PUBLIC_KEYS.PK_TIME_EXPIRES)),
              record.get(PUBLIC_KEYS.PK_FINGERPRINT)
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
