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

import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPPublicKey;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.PUBLIC_KEYS;

/**
 * Update an SCM provider.
 */

public final class NPDBQPublicKeyPut
  extends NPDBQAbstract<NPPublicKey, NPDatabaseUnit>
  implements NPDatabaseQueriesPublicKeysType.PutType
{
  private static final Service<NPPublicKey, NPDatabaseUnit, PutType> SERVICE =
    new Service<>(PutType.class, NPDBQPublicKeyPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPublicKeyPut(
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
    final NPPublicKey key)
  {
    final var userIdArray = new String[key.userIDs().size()];
    key.userIDs().toArray(userIdArray);

    final var query =
      context.insertInto(PUBLIC_KEYS)
        .set(PUBLIC_KEYS.PK_USER_IDS, userIdArray)
        .set(PUBLIC_KEYS.PK_FINGERPRINT, key.fingerprint().value())
        .set(PUBLIC_KEYS.PK_TIME_CREATED, key.timeCreated())
        .set(PUBLIC_KEYS.PK_TIME_EXPIRES, key.timeExpires().orElse(null))
        .set(PUBLIC_KEYS.PK_ENCODED, key.encodedForm())
        .onConflict(PUBLIC_KEYS.PK_FINGERPRINT)
        .doUpdate()
        .set(PUBLIC_KEYS.PK_USER_IDS, userIdArray)
        .set(PUBLIC_KEYS.PK_FINGERPRINT, key.fingerprint().value())
        .set(PUBLIC_KEYS.PK_TIME_CREATED, key.timeCreated())
        .set(PUBLIC_KEYS.PK_TIME_EXPIRES, key.timeExpires().orElse(null))
        .set(PUBLIC_KEYS.PK_ENCODED, key.encodedForm());

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
