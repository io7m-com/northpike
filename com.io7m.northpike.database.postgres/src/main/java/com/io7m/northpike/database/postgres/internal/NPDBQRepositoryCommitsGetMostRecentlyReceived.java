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

import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;

/**
 * Get the most recently received commit in the repository.
 */

public final class NPDBQRepositoryCommitsGetMostRecentlyReceived
  extends NPDBQAbstract<UUID, Optional<NPCommitSummary>>
  implements NPDatabaseQueriesRepositoriesType.CommitsGetMostRecentlyReceivedType
{
  private static final Service<UUID, Optional<NPCommitSummary>, CommitsGetMostRecentlyReceivedType> SERVICE =
    new Service<>(
      CommitsGetMostRecentlyReceivedType.class,
      NPDBQRepositoryCommitsGetMostRecentlyReceived::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryCommitsGetMostRecentlyReceived(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPCommitSummary> onExecute(
    final DSLContext context,
    final UUID parameters)
    throws NPDatabaseException
  {
    final var query =
      context.select(
          DSL.max(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED),
          REPOSITORY_COMMITS.RC_COMMIT_ID,
          REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT,
          REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED,
          REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED
        ).from(REPOSITORY_COMMITS)
        .where(REPOSITORY_COMMITS.RC_REPOSITORY.eq(parameters))
        .groupBy(
          REPOSITORY_COMMITS.RC_COMMIT_ID,
          REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT,
          REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED,
          REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED
        )
        .limit(Integer.valueOf(1));

    recordQuery(query);
    return query.fetchOptional()
      .map(rec -> {
        final var commit =
          new NPCommitID(
            parameters,
            new NPCommitUnqualifiedID(rec.get(REPOSITORY_COMMITS.RC_COMMIT_ID))
          );

        return new NPCommitSummary(
          commit,
          rec.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED),
          rec.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED),
          rec.get(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT)
        );
      });
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }


}
