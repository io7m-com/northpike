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
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyUnassignType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.postgres.internal.Tables.PUBLIC_KEYS;
import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORY_KEYS;
import static com.io7m.northpike.strings.NPStringConstants.PUBLIC_KEY;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;
import static java.util.Map.entry;

/**
 * Unassign a public key.
 */

public final class NPDBQRepositoryPublicKeyUnassign
  extends NPDBQAbstract<RepositoryPublicKeyUnassignType.Parameters, NPDatabaseUnit>
  implements RepositoryPublicKeyUnassignType
{
  private static final Service<
    RepositoryPublicKeyUnassignType.Parameters,
    NPDatabaseUnit,
    RepositoryPublicKeyUnassignType>
    SERVICE =
    new Service<>(
      RepositoryPublicKeyUnassignType.class,
      NPDBQRepositoryPublicKeyUnassign::new
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryPublicKeyUnassign(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final RepositoryPublicKeyUnassignType.Parameters parameters)
    throws NPDatabaseException
  {
    this.setAttribute(REPOSITORY, parameters.repositoryId().toString());
    this.setAttribute(PUBLIC_KEY, parameters.key().value());

    final var keyId =
      context.select(PUBLIC_KEYS.PK_ID)
        .from(PUBLIC_KEYS)
        .where(PUBLIC_KEYS.PK_FINGERPRINT.eq(parameters.key().value()));

    final var query =
      context.deleteFrom(REPOSITORY_KEYS)
        .where(
          REPOSITORY_KEYS.RK_KEY.eq(keyId)
            .and(REPOSITORY_KEYS.RK_REPOSITORY.eq(
              parameters.repositoryId().value()))
        );

    recordQuery(query);
    query.execute();

    this.auditEventPut(
      context,
      "PUBLIC_KEY_UNASSIGN",
      entry("KEY", parameters.key().value()),
      entry("REPOSITORY", parameters.repositoryId().toString())
    );
    return NPDatabaseUnit.UNIT;
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
