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
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitAuthor;
import com.io7m.northpike.model.NPCommitID;
import org.jooq.DSLContext;

import java.time.OffsetDateTime;
import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_AUTHORS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_BRANCHES;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_TAGS;

/**
 * Get a commit.
 */

public final class NPDBQRepositoryCommitGet
  extends NPDBQAbstract<NPCommitID, Optional<NPCommit>>
  implements RepositoryCommitGetType
{
  private static final Service<NPCommitID, Optional<NPCommit>, RepositoryCommitGetType> SERVICE =
    new Service<>(RepositoryCommitGetType.class, NPDBQRepositoryCommitGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryCommitGet(
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
  protected Optional<NPCommit> onExecute(
    final DSLContext context,
    final NPCommitID id)
    throws NPDatabaseException
  {
    final var query =
      context.select(
          REPOSITORY_COMMITS.RC_COMMIT_ID,
          REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED,
          REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED,
          REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT,
          REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_BODY,
          REPOSITORY_COMMIT_AUTHORS.RCA_EMAIL,
          REPOSITORY_COMMIT_AUTHORS.RCA_NAME,
          REPOSITORY_COMMIT_BRANCHES.RCB_BRANCH,
          REPOSITORY_COMMIT_TAGS.RCT_TAG)
        .from(REPOSITORY_COMMITS)
        .join(REPOSITORY_COMMIT_AUTHORS)
        .on(REPOSITORY_COMMITS.RC_COMMIT_AUTHOR.eq(REPOSITORY_COMMIT_AUTHORS.RCA_ID))
        .leftOuterJoin(REPOSITORY_COMMIT_BRANCHES)
        .on(REPOSITORY_COMMITS.RC_ID.eq(REPOSITORY_COMMIT_BRANCHES.RCB_COMMIT))
        .leftOuterJoin(REPOSITORY_COMMIT_TAGS)
        .on(REPOSITORY_COMMITS.RC_ID.eq(REPOSITORY_COMMIT_TAGS.RCT_COMMIT))
        .where(
          REPOSITORY_COMMITS.RC_REPOSITORY.eq(id.repository().value())
            .and(REPOSITORY_COMMITS.RC_COMMIT_ID.eq(id.commitId().value()))
        );

    recordQuery(query);
    final var records = query.fetch();
    if (records.isEmpty()) {
      return Optional.empty();
    }

    OffsetDateTime timeCreated = null;
    OffsetDateTime timeReceived = null;
    NPCommitAuthor author = null;
    String messageSubject = null;
    String messageBody = null;
    final Set<String> branches = new HashSet<>();
    final Set<String> tags = new HashSet<>();

    for (final var result : records) {
      timeCreated =
        Objects.requireNonNullElse(
          result.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED),
          timeCreated
        );
      timeReceived =
        Objects.requireNonNullElse(
          result.get(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED),
          timeReceived
        );
      messageSubject =
        Objects.requireNonNullElse(
          result.get(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT),
          messageSubject
        );
      messageBody =
        Objects.requireNonNullElse(
          result.get(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_BODY),
          messageBody
        );
      author =
        new NPCommitAuthor(
          result.get(REPOSITORY_COMMIT_AUTHORS.RCA_NAME),
          result.get(REPOSITORY_COMMIT_AUTHORS.RCA_EMAIL)
        );

      final var b = result.get(REPOSITORY_COMMIT_BRANCHES.RCB_BRANCH);
      if (b != null) {
        branches.add(b);
      }

      final var t = result.get(REPOSITORY_COMMIT_TAGS.RCT_TAG);
      if (t != null) {
        tags.add(t);
      }
    }

    return Optional.of(new NPCommit(
      id,
      timeCreated,
      timeReceived,
      author,
      messageSubject,
      messageBody,
      branches,
      tags
    ));
  }

}
