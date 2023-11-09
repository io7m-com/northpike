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
import com.io7m.northpike.database.api.NPAgentLoginChallengePagedType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.LoginChallengeSearchType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448Type;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeSearchParameters;
import io.opentelemetry.api.trace.Span;
import org.jooq.DSLContext;
import org.jooq.Record;
import org.jooq.exception.DataAccessException;
import org.jooq.impl.DSL;

import java.util.ArrayList;
import java.util.List;

import static com.io7m.jqpage.core.JQOrder.ASCENDING;
import static com.io7m.northpike.database.postgres.internal.NPDatabaseExceptions.handleDatabaseException;
import static com.io7m.northpike.database.postgres.internal.tables.AgentLoginChallenges.AGENT_LOGIN_CHALLENGES;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

/**
 * Search for login challenges.
 */

public final class NPDBQAgentLoginChallengeSearch
  extends NPDBQAbstract<NPAgentLoginChallengeSearchParameters, NPAgentLoginChallengePagedType>
  implements LoginChallengeSearchType
{
  private static final Service<
    NPAgentLoginChallengeSearchParameters,
    NPAgentLoginChallengePagedType,
    LoginChallengeSearchType> SERVICE =
    new Service<>(
      LoginChallengeSearchType.class,
      NPDBQAgentLoginChallengeSearch::new);

  private static final NPAgentKeyPairFactoryEd448Type ED448_KEYS =
    new NPAgentKeyPairFactoryEd448();

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentLoginChallengeSearch(
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
  protected NPAgentLoginChallengePagedType onExecute(
    final DSLContext context,
    final NPAgentLoginChallengeSearchParameters parameters)
    throws NPDatabaseException
  {
    final var timeCondition =
      AGENT_LOGIN_CHALLENGES.ALC_CREATED.ge(parameters.timeRange().lower())
        .and(AGENT_LOGIN_CHALLENGES.ALC_CREATED.le(parameters.timeRange().upper()));

    final var allConditions =
      DSL.and(timeCondition);

    final var pageParameters =
      JQKeysetRandomAccessPaginationParameters.forTable(AGENT_LOGIN_CHALLENGES)
        .addSortField(new JQField(
          AGENT_LOGIN_CHALLENGES.ALC_CREATED,
          ASCENDING))
        .addWhereCondition(allConditions)
        .setDistinct(JQSelectDistinct.SELECT)
        .setPageSize(parameters.pageSize())
        .setStatementListener(statement -> {
          Span.current().setAttribute(DB_STATEMENT, statement.toString());
        }).build();

    final var pages =
      JQKeysetRandomAccessPagination.createPageDefinitions(
        context, pageParameters);

    return new NPAgentLoginChallengeSearch(pages);
  }

  private static final class NPAgentLoginChallengeSearch
    extends NPAbstractSearch<NPAgentLoginChallengeRecord>
    implements NPAgentLoginChallengePagedType
  {
    NPAgentLoginChallengeSearch(
      final List<JQKeysetRandomAccessPageDefinition> pages)
    {
      super(pages);
    }

    @Override
    protected NPPage<NPAgentLoginChallengeRecord> page(
      final NPDatabaseTransaction transaction,
      final JQKeysetRandomAccessPageDefinition page)
      throws NPDatabaseException
    {
      final var context =
        transaction.createContext();
      final var querySpan =
        transaction.createQuerySpan(
          "NPAgentLoginChallengeSearch.page");

      try {
        final var query =
          page.queryFields(context, List.of(
            AGENT_LOGIN_CHALLENGES.ALC_CHALLENGE,
            AGENT_LOGIN_CHALLENGES.ALC_CREATED,
            AGENT_LOGIN_CHALLENGES.ALC_ID,
            AGENT_LOGIN_CHALLENGES.ALC_KEY_ALGO,
            AGENT_LOGIN_CHALLENGES.ALC_KEY_DATA,
            AGENT_LOGIN_CHALLENGES.ALC_SOURCE
          ));

        querySpan.setAttribute(DB_STATEMENT, query.toString());

        final var results = new ArrayList<NPAgentLoginChallengeRecord>();
        for (final var item : query.fetch()) {
          results.add(mapRecord(item));
        }

        return new NPPage<>(
          List.copyOf(results),
          (int) page.index(),
          this.pageCount(),
          page.firstOffset()
        );
      } catch (final DataAccessException e) {
        querySpan.recordException(e);
        throw handleDatabaseException(transaction, e);
      } catch (final NPException e) {
        querySpan.recordException(e);
        throw new NPDatabaseException(
          e.getMessage(),
          e,
          e.errorCode(),
          e.attributes(),
          e.remediatingAction()
        );
      } finally {
        querySpan.end();
      }
    }

    private static NPAgentLoginChallengeRecord mapRecord(
      final Record r)
      throws NPException
    {
      final var algo =
        r.get(AGENT_LOGIN_CHALLENGES.ALC_KEY_ALGO);

      final var key =
        switch (algo) {
          case "Ed448" -> {
            yield ED448_KEYS.parsePublicKeyFromText(
              r.get(AGENT_LOGIN_CHALLENGES.ALC_KEY_DATA)
            );
          }
          default -> {
            throw new IllegalStateException(
              "Unrecognized algorithm: %s".formatted(algo)
            );
          }
        };

      return new NPAgentLoginChallengeRecord(
        r.get(AGENT_LOGIN_CHALLENGES.ALC_CREATED),
        r.get(AGENT_LOGIN_CHALLENGES.ALC_SOURCE),
        key,
        new NPAgentLoginChallenge(
          r.get(AGENT_LOGIN_CHALLENGES.ALC_ID),
          r.get(AGENT_LOGIN_CHALLENGES.ALC_CHALLENGE)
        )
      );
    }
  }
}
