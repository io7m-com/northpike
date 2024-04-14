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
import com.io7m.northpike.model.NPFingerprint;
import org.jooq.DSLContext;
import org.jooq.Query;

import java.util.ArrayList;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.PUBLIC_KEYS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_KEYS;
import static java.util.Map.entry;

/**
 * Update an SCM provider.
 */

public final class NPDBQPublicKeyDelete
  extends NPDBQAbstract<NPFingerprint, NPDatabaseUnit>
  implements NPDatabaseQueriesPublicKeysType.PublicKeyDeleteType
{
  private static final Service<NPFingerprint, NPDatabaseUnit, PublicKeyDeleteType> SERVICE =
    new Service<>(PublicKeyDeleteType.class, NPDBQPublicKeyDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPublicKeyDelete(
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
    final NPFingerprint key)
  {
    final var batches = new ArrayList<Query>();

    final var findKey =
      context.select(PUBLIC_KEYS.PK_ID)
        .from(PUBLIC_KEYS)
        .where(PUBLIC_KEYS.PK_FINGERPRINT.eq(key.value()));

    batches.add(
      context.deleteFrom(REPOSITORY_KEYS)
        .where(REPOSITORY_KEYS.RK_KEY.eq(findKey))
    );

    batches.add(
      context.deleteFrom(PUBLIC_KEYS)
        .where(PUBLIC_KEYS.PK_FINGERPRINT.eq(key.value()))
    );

    context.batch(batches)
      .execute();

    this.auditEventPut(
      context,
      "PUBLIC_KEY_DELETE",
      entry("KEY", key.value())
    );
    return UNIT;
  }
}
