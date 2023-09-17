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


import com.io7m.northpike.database.api.NPDatabaseQueriesArchivesType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPArchive;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.ARCHIVES;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;
import static com.io7m.northpike.strings.NPStringConstants.ARCHIVE;
import static com.io7m.northpike.strings.NPStringConstants.COMMIT;

/**
 * Update an archive.
 */

public final class NPDBQArchivePut
  extends NPDBQAbstract<NPArchive, NPDatabaseUnit>
  implements NPDatabaseQueriesArchivesType.PutType
{
  private static final Service<NPArchive, NPDatabaseUnit, PutType> SERVICE =
    new Service<>(PutType.class, NPDBQArchivePut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQArchivePut(
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
    final NPArchive archive)
  {
    final var commitVal = archive.commit();
    this.setAttribute(ARCHIVE, archive.token().value());
    this.setAttribute(COMMIT, commitVal.commitId().value());

    final var commit =
      context.select(REPOSITORY_COMMITS.RC_ID)
        .from(REPOSITORY_COMMITS)
        .where(
          REPOSITORY_COMMITS.RC_COMMIT_ID.eq(commitVal.commitId().value())
            .and(REPOSITORY_COMMITS.RC_REPOSITORY.eq(commitVal.repository()))
        );

    final var query =
      context.insertInto(ARCHIVES)
        .set(ARCHIVES.AR_COMMIT, commit)
        .set(ARCHIVES.AR_CREATED, archive.created())
        .set(ARCHIVES.AR_HASH_ALGO, archive.hash().algorithm())
        .set(ARCHIVES.AR_HASH_VALUE, archive.hash().value())
        .set(ARCHIVES.AR_TOKEN, archive.token().value())
        .onConflictOnConstraint(DSL.name("archives_token_unique"))
        .doUpdate()
        .set(ARCHIVES.AR_COMMIT, commit)
        .set(ARCHIVES.AR_CREATED, archive.created())
        .set(ARCHIVES.AR_HASH_ALGO, archive.hash().algorithm())
        .set(ARCHIVES.AR_HASH_VALUE, archive.hash().value())
        .set(ARCHIVES.AR_TOKEN, archive.token().value());

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
