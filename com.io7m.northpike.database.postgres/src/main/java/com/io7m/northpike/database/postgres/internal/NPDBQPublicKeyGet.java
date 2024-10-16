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


import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType.PublicKeyGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKey;
import org.jooq.DSLContext;

import java.util.Optional;
import java.util.Set;

import static com.io7m.northpike.database.postgres.internal.Tables.PUBLIC_KEYS;

/**
 * Retrieve an SCM provider.
 */

public final class NPDBQPublicKeyGet
  extends NPDBQAbstract<NPFingerprint, Optional<NPPublicKey>>
  implements PublicKeyGetType
{
  private static final Service<NPFingerprint, Optional<NPPublicKey>, PublicKeyGetType> SERVICE =
    new Service<>(PublicKeyGetType.class, NPDBQPublicKeyGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPublicKeyGet(
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
  protected Optional<NPPublicKey> onExecute(
    final DSLContext context,
    final NPFingerprint name)
  {
    final var query =
      context.select(
          PUBLIC_KEYS.PK_FINGERPRINT,
          PUBLIC_KEYS.PK_ENCODED,
          PUBLIC_KEYS.PK_TIME_CREATED,
          PUBLIC_KEYS.PK_TIME_EXPIRES,
          PUBLIC_KEYS.PK_USER_IDS
        ).from(PUBLIC_KEYS)
        .where(PUBLIC_KEYS.PK_FINGERPRINT.eq(name.value()));

    recordQuery(query);
    return query.fetchOptional().map(NPDBQPublicKeyGet::mapKey);
  }

  private static NPPublicKey mapKey(
    final org.jooq.Record r)
  {
    return new NPPublicKey(
      Set.of(r.get(PUBLIC_KEYS.PK_USER_IDS)),
      new NPFingerprint(r.get(PUBLIC_KEYS.PK_FINGERPRINT)),
      r.get(PUBLIC_KEYS.PK_TIME_CREATED),
      Optional.ofNullable(r.get(PUBLIC_KEYS.PK_TIME_EXPIRES)),
      r.get(PUBLIC_KEYS.PK_ENCODED)
    );
  }
}
