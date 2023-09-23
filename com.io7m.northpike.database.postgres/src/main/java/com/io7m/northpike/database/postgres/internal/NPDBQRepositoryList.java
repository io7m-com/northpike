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
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.api.NPRepositoriesPagedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryCredentialsType;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.northpike.model.NPRepositoryDescription;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.Record;
import org.jooq.exception.DataAccessException;

import java.net.URI;
import java.util.List;

import static com.io7m.northpike.database.postgres.internal.NPDBQRepositoryGet.signingPolicy;
import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.Tables.SCM_PROVIDERS;
import static com.io7m.northpike.database.postgres.internal.tables.Repositories.REPOSITORIES;
import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * List repositories.
 */

public final class NPDBQRepositoryList
  extends NPDBQAbstract<NPDatabaseUnit, NPRepositoriesPagedType>
  implements NPDatabaseQueriesRepositoriesType.ListType
{
  private static final Service<NPDatabaseUnit, NPRepositoriesPagedType, ListType> SERVICE =
    new Service<>(ListType.class, NPDBQRepositoryList::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryList(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPRepositoriesPagedType onExecute(
    final DSLContext context,
    final NPDatabaseUnit parameters)
    throws NPDatabaseException
  {
    final var tableSource =
      REPOSITORIES
        .join(SCM_PROVIDERS)
        .on(REPOSITORIES.R_PROVIDER.eq(SCM_PROVIDERS.SP_ID));

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(tableSource)
        .addSortField(new JQField(REPOSITORIES.R_URL, JQOrder.ASCENDING))
        .setDistinct(JQSelectDistinct.SELECT_DISTINCT)
        .setPageSize(100L)
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPDBQRepositoryList.NPRepositoryList(pages);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  static final class NPRepositoryList
    extends NPAbstractSearch<NPRepositoryDescription>
    implements NPRepositoriesPagedType
  {
    NPRepositoryList(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPRepositoryDescription> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPRepositoryList.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            REPOSITORIES.R_ID,
            REPOSITORIES.R_URL,
            REPOSITORIES.R_PROVIDER,
            REPOSITORIES.R_CREDENTIALS_TYPE,
            REPOSITORIES.R_CREDENTIALS_USERNAME,
            REPOSITORIES.R_CREDENTIALS_PASSWORD,
            REPOSITORIES.R_SIGNING_POLICY,
            SCM_PROVIDERS.SP_NAME
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var items =
          query.fetch().map(record -> {
            return new NPRepositoryDescription(
              new RDottedName(record.get(SCM_PROVIDERS.SP_NAME)),
              record.get(REPOSITORIES.R_ID),
              URI.create(record.get(REPOSITORIES.R_URL)),
              mapCredentials(record),
              signingPolicy(record.get(REPOSITORIES.R_SIGNING_POLICY))
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

    private static NPRepositoryCredentialsType mapCredentials(
      final Record record)
    {
      return switch (record.get(REPOSITORIES.R_CREDENTIALS_TYPE)) {
        case REPOSITORY_CREDENTIALS_USERNAME_PASSWORD -> {
          yield new NPRepositoryCredentialsUsernamePassword(
            record.get(REPOSITORIES.R_CREDENTIALS_USERNAME),
            record.get(REPOSITORIES.R_CREDENTIALS_PASSWORD)
          );
        }
        case REPOSITORY_CREDENTIALS_NONE -> {
          yield CREDENTIALS_NONE;
        }
      };
    }
  }
}
