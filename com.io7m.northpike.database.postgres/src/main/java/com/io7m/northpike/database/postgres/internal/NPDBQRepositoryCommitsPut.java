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
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsPutType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitLink;
import org.jooq.DSLContext;
import org.jooq.Query;
import org.jooq.impl.DSL;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Locale;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_AUTHORS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_BRANCHES;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_LINKS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMIT_TAGS;

/**
 * Update commits in a repository.
 */

public final class NPDBQRepositoryCommitsPut
  extends NPDBQAbstract<CommitsPutType.Parameters, NPDatabaseUnit>
  implements CommitsPutType
{
  private static final Service<CommitsPutType.Parameters, NPDatabaseUnit, CommitsPutType> SERVICE =
    new Service<>(CommitsPutType.class, NPDBQRepositoryCommitsPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryCommitsPut(
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
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final CommitsPutType.Parameters description)
    throws NPDatabaseException
  {
    final var commitGraph =
      description.commitGraph();
    final var queries =
      new ArrayList<Query>(commitGraph.linksByCommit().size());

    for (final var commit : description.commits()) {
      queries.add(insertAuthor(context, commit));
      queries.add(insertCommit(context, commit));
      queries.addAll(insertCommitTags(context, commit));
      queries.addAll(insertCommitBranches(context, commit));
    }

    for (final var link : commitGraph.linksByCommit()) {
      queries.add(insertCommitLink(context, link));
    }

    recordQuery(queries);
    context.batch(queries).execute();
    return UNIT;
  }

  private static Query insertAuthor(
    final DSLContext context,
    final NPCommit commit)
  {
    final var author =
      commit.author();
    final var emailLower =
      author.authorEmail().toLowerCase(Locale.ROOT);

    return context.insertInto(REPOSITORY_COMMIT_AUTHORS)
      .set(REPOSITORY_COMMIT_AUTHORS.RCA_EMAIL, emailLower)
      .set(REPOSITORY_COMMIT_AUTHORS.RCA_NAME, author.authorName())
      .onConflictDoNothing();
  }

  private static Collection<? extends Query> insertCommitTags(
    final DSLContext context,
    final NPCommit commit)
  {
    final var queries = new ArrayList<Query>();

    final var commitSelect =
      context.select(REPOSITORY_COMMITS.RC_ID)
        .from(REPOSITORY_COMMITS)
        .where(
          REPOSITORY_COMMITS.RC_COMMIT_ID.eq(commit.id().commitId().value())
            .and(REPOSITORY_COMMITS.RC_REPOSITORY.eq(commit.id().repository()))
        );

    queries.add(
      context.deleteFrom(REPOSITORY_COMMIT_TAGS)
        .where(REPOSITORY_COMMIT_TAGS.RCT_COMMIT.eq(commitSelect))
    );

    for (final var tag : commit.tags()) {
      queries.add(
        context.insertInto(REPOSITORY_COMMIT_TAGS)
          .set(REPOSITORY_COMMIT_TAGS.RCT_TAG, tag)
          .set(REPOSITORY_COMMIT_TAGS.RCT_COMMIT, commitSelect)
      );
    }

    return queries;
  }

  private static Collection<? extends Query> insertCommitBranches(
    final DSLContext context,
    final NPCommit commit)
  {
    final var queries = new ArrayList<Query>();

    final var commitSelect =
      context.select(REPOSITORY_COMMITS.RC_ID)
        .from(REPOSITORY_COMMITS)
        .where(
          REPOSITORY_COMMITS.RC_COMMIT_ID.eq(commit.id().commitId().value())
            .and(REPOSITORY_COMMITS.RC_REPOSITORY.eq(commit.id().repository()))
        );

    queries.add(
      context.deleteFrom(REPOSITORY_COMMIT_BRANCHES)
        .where(REPOSITORY_COMMIT_BRANCHES.RCB_COMMIT.eq(commitSelect))
    );

    for (final var branch : commit.branches()) {
      queries.add(
        context.insertInto(REPOSITORY_COMMIT_BRANCHES)
          .set(REPOSITORY_COMMIT_BRANCHES.RCB_COMMIT, commitSelect)
          .set(REPOSITORY_COMMIT_BRANCHES.RCB_BRANCH, branch)
          .onConflictDoNothing()
      );
    }

    return queries;
  }

  private static Query insertCommitLink(
    final DSLContext context,
    final NPCommitLink link)
  {
    final var selectMain =
      context.select(REPOSITORY_COMMITS.RC_ID)
        .from(REPOSITORY_COMMITS)
        .where(
          REPOSITORY_COMMITS.RC_COMMIT_ID.eq(link.commit().commitId().value())
            .and(REPOSITORY_COMMITS.RC_REPOSITORY.eq(link.commit().repository()))
        );

    return link.next()
      .map(next -> {
        final var selectNext =
          context.select(REPOSITORY_COMMITS.RC_ID)
            .from(REPOSITORY_COMMITS)
            .where(
              REPOSITORY_COMMITS.RC_COMMIT_ID.eq(next.commitId().value())
                .and(REPOSITORY_COMMITS.RC_REPOSITORY.eq(next.repository()))
            );

        return (Query) context.insertInto(REPOSITORY_COMMIT_LINKS)
          .set(REPOSITORY_COMMIT_LINKS.RCL_COMMIT, selectMain)
          .set(REPOSITORY_COMMIT_LINKS.RCL_COMMIT_NEXT, selectNext)
          .onConflictOnConstraint(DSL.name("repository_commit_links_primary_key"))
          .doNothing();
      }).orElseGet(() -> {
        return context.deleteFrom(REPOSITORY_COMMIT_LINKS)
          .where(REPOSITORY_COMMIT_LINKS.RCL_COMMIT.eq(selectMain));
      });
  }

  private static Query insertCommit(
    final DSLContext context,
    final NPCommit com)
  {
    final var author = com.author();
    final var authorSelect =
      context.select(REPOSITORY_COMMIT_AUTHORS.RCA_ID)
        .from(REPOSITORY_COMMIT_AUTHORS)
        .where(
          REPOSITORY_COMMIT_AUTHORS.RCA_EMAIL.eq(author.authorEmail())
            .and(REPOSITORY_COMMIT_AUTHORS.RCA_NAME.eq(author.authorName()))
        );

    return context.insertInto(REPOSITORY_COMMITS)
      .set(REPOSITORY_COMMITS.RC_COMMIT_AUTHOR, authorSelect)
      .set(REPOSITORY_COMMITS.RC_COMMIT_ID, com.id().commitId().value())
      .set(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT, com.messageSubject())
      .set(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_BODY, com.messageBody())
      .set(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED, com.timeCreated())
      .set(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED, com.timeReceived())
      .set(REPOSITORY_COMMITS.RC_REPOSITORY, com.id().repository())
      .onConflictOnConstraint(DSL.name("repository_commits_unique"))
      .doUpdate()
      .set(REPOSITORY_COMMITS.RC_COMMIT_AUTHOR, authorSelect)
      .set(REPOSITORY_COMMITS.RC_COMMIT_ID, com.id().commitId().value())
      .set(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_SUBJECT, com.messageSubject())
      .set(REPOSITORY_COMMITS.RC_COMMIT_MESSAGE_BODY, com.messageBody())
      .set(REPOSITORY_COMMITS.RC_COMMIT_TIME_CREATED, com.timeCreated())
      .set(REPOSITORY_COMMITS.RC_COMMIT_TIME_RECEIVED, com.timeReceived())
      .set(REPOSITORY_COMMITS.RC_REPOSITORY, com.id().repository());
  }
}
