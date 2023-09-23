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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.GetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.database.postgres.internal.enums.RepositorySigningPolicyT;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import org.jooq.DSLContext;

import java.net.URI;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.Tables.REPOSITORIES;
import static com.io7m.northpike.database.postgres.internal.Tables.SCM_PROVIDERS;

/**
 * Retrieve a repository.
 */

public final class NPDBQRepositoryGet
  extends NPDBQAbstract<UUID, Optional<NPRepositoryDescription>>
  implements GetType
{
  private static final Service<UUID, Optional<NPRepositoryDescription>, GetType> SERVICE =
    new Service<>(GetType.class, NPDBQRepositoryGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryGet(
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
  protected Optional<NPRepositoryDescription> onExecute(
    final DSLContext context,
    final UUID name)
  {
    final var query =
      context.select(
          REPOSITORIES.R_ID,
          REPOSITORIES.R_URL,
          REPOSITORIES.R_CREDENTIALS_TYPE,
          REPOSITORIES.R_CREDENTIALS_USERNAME,
          REPOSITORIES.R_CREDENTIALS_PASSWORD,
          REPOSITORIES.R_SIGNING_POLICY,
          SCM_PROVIDERS.SP_NAME
        ).from(REPOSITORIES)
        .join(SCM_PROVIDERS)
        .on(SCM_PROVIDERS.SP_ID.eq(REPOSITORIES.R_PROVIDER))
        .where(REPOSITORIES.R_ID.eq(name));

    recordQuery(query);
    return query.fetchOptional().map(NPDBQRepositoryGet::mapRepository);
  }

  private static NPRepositoryDescription mapRepository(
    final org.jooq.Record r)
  {
    final var credentials =
      switch (r.get(REPOSITORIES.R_CREDENTIALS_TYPE)) {
        case REPOSITORY_CREDENTIALS_NONE -> {
          yield NPRepositoryCredentialsNone.CREDENTIALS_NONE;
        }
        case REPOSITORY_CREDENTIALS_USERNAME_PASSWORD -> {
          yield new NPRepositoryCredentialsUsernamePassword(
            r.get(REPOSITORIES.R_CREDENTIALS_USERNAME),
            r.get(REPOSITORIES.R_CREDENTIALS_PASSWORD)
          );
        }
      };

    return new NPRepositoryDescription(
      new RDottedName(r.get(SCM_PROVIDERS.SP_NAME)),
      r.get(REPOSITORIES.R_ID),
      URI.create(r.get(REPOSITORIES.R_URL)),
      credentials,
      signingPolicy(r.get(REPOSITORIES.R_SIGNING_POLICY))
    );
  }

  static NPRepositorySigningPolicy signingPolicy(
    final RepositorySigningPolicyT r)
  {
    return switch (r) {
      case REPOSITORY_ALLOW_UNSIGNED_COMMITS ->
        NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
      case REPOSITORY_REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY ->
        NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY;
      case REPOSITORY_REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS ->
        NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;
    };
  }
}
