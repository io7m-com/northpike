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
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.PublicKeysAssignedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPRepositoryID;
import org.jooq.DSLContext;

import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.postgres.internal.Tables.PUBLIC_KEYS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_KEYS;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;

/**
 * Retrieve the keys assigned to a repository.
 */

public final class NPDBQRepositoryPublicKeysAssigned
  extends NPDBQAbstract<NPRepositoryID, Set<NPFingerprint>>
  implements PublicKeysAssignedType
{
  private static final Service<NPRepositoryID, Set<NPFingerprint>, PublicKeysAssignedType> SERVICE =
    new Service<>(
      PublicKeysAssignedType.class,
      NPDBQRepositoryPublicKeysAssigned::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryPublicKeysAssigned(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Set<NPFingerprint> onExecute(
    final DSLContext context,
    final NPRepositoryID id)
    throws NPDatabaseException
  {
    this.setAttribute(REPOSITORY, id.toString());

    return context.select(PUBLIC_KEYS.PK_FINGERPRINT)
      .from(PUBLIC_KEYS)
      .join(REPOSITORY_KEYS)
      .on(REPOSITORY_KEYS.RK_KEY.eq(PUBLIC_KEYS.PK_ID))
      .where(REPOSITORY_KEYS.RK_REPOSITORY.eq(id.value()))
      .stream()
      .map(r -> new NPFingerprint(r.get(PUBLIC_KEYS.PK_FINGERPRINT)))
      .collect(Collectors.toUnmodifiableSet());
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
