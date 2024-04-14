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
import com.io7m.northpike.database.api.NPDatabaseQueriesArchivesType.ArchiveGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitUnqualifiedID;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPToken;
import org.jooq.DSLContext;
import org.jooq.Record6;

import java.time.OffsetDateTime;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.Tables.ARCHIVES;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_COMMITS;

/**
 * Retrieve an archive.
 */

public final class NPDBQArchiveGet
  extends NPDBQAbstract<NPToken, Optional<NPArchive>>
  implements ArchiveGetType
{
  private static final Service<NPToken, Optional<NPArchive>, ArchiveGetType> SERVICE =
    new Service<>(ArchiveGetType.class, NPDBQArchiveGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQArchiveGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPArchive> onExecute(
    final DSLContext context,
    final NPToken token)
    throws NPDatabaseException
  {
    return context.select(
      ARCHIVES.AR_TOKEN,
      ARCHIVES.AR_HASH_ALGO,
      ARCHIVES.AR_HASH_VALUE,
      ARCHIVES.AR_CREATED,
      REPOSITORY_COMMITS.RC_REPOSITORY,
      REPOSITORY_COMMITS.RC_COMMIT_ID
    ).from(ARCHIVES)
      .join(REPOSITORY_COMMITS)
      .on(REPOSITORY_COMMITS.RC_ID.eq(ARCHIVES.AR_COMMIT))
      .where(ARCHIVES.AR_TOKEN.eq(token.value()))
      .fetchOptional()
      .map(NPDBQArchiveGet::mapRecord);
  }

  private static NPArchive mapRecord(
    final Record6<String, String, String, OffsetDateTime, UUID, String> r)
  {
    return new NPArchive(
      new NPToken(r.get(ARCHIVES.AR_TOKEN)),
      new NPCommitID(
        new NPRepositoryID(r.get(REPOSITORY_COMMITS.RC_REPOSITORY)),
        new NPCommitUnqualifiedID(r.get(REPOSITORY_COMMITS.RC_COMMIT_ID))
      ),
      new NPHash(
        r.get(ARCHIVES.AR_HASH_ALGO),
        r.get(ARCHIVES.AR_HASH_VALUE)
      ),
      r.get(ARCHIVES.AR_CREATED)
    );
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }
}
