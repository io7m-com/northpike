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


import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.database.postgres.internal.enums.RepositoryCredentialsTypeT;
import com.io7m.northpike.database.postgres.internal.enums.RepositorySigningPolicyT;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryCredentialsType;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.enums.RepositoryCredentialsTypeT.REPOSITORY_CREDENTIALS_NONE;
import static com.io7m.northpike.database.postgres.internal.enums.RepositoryCredentialsTypeT.REPOSITORY_CREDENTIALS_USERNAME_PASSWORD;
import static com.io7m.northpike.database.postgres.internal.tables.Repositories.REPOSITORIES;
import static com.io7m.northpike.database.postgres.internal.tables.ScmProviders.SCM_PROVIDERS;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;
import static com.io7m.northpike.strings.NPStringConstants.SCM_PROVIDER;
import static java.util.Map.entry;

/**
 * Update a repository.
 */

public final class NPDBQRepositoryPut
  extends NPDBQAbstract<NPRepositoryDescription, NPDatabaseUnit>
  implements NPDatabaseQueriesRepositoriesType.PutType
{
  private static final Service<NPRepositoryDescription, NPDatabaseUnit, PutType> SERVICE =
    new Service<>(PutType.class, NPDBQRepositoryPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQRepositoryPut(
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
    final NPRepositoryDescription description)
  {
    this.setAttribute(SCM_PROVIDER, description.provider().value());
    this.setAttribute(REPOSITORY, description.url().toString());

    final var selectedProvider =
      context.select(SCM_PROVIDERS.SP_ID)
        .from(SCM_PROVIDERS)
        .where(SCM_PROVIDERS.SP_NAME.eq(description.provider().value()));

    final var query =
      context.insertInto(REPOSITORIES)
        .set(REPOSITORIES.R_ID, description.id().value())
        .set(REPOSITORIES.R_PROVIDER, selectedProvider)
        .set(REPOSITORIES.R_URL, description.url().toString())
        .set(
          REPOSITORIES.R_CREDENTIALS_TYPE,
          credentialsType(description.credentials()))
        .set(
          REPOSITORIES.R_CREDENTIALS_USERNAME,
          credentialsUsername(description.credentials()))
        .set(
          REPOSITORIES.R_CREDENTIALS_PASSWORD,
          credentialsPassword(description.credentials()))
        .set(
          REPOSITORIES.R_SIGNING_POLICY,
          signingPolicy(description.signingPolicy()))
        .onConflict(REPOSITORIES.R_URL)
        .doUpdate()
        .set(REPOSITORIES.R_ID, description.id().value())
        .set(REPOSITORIES.R_PROVIDER, selectedProvider)
        .set(REPOSITORIES.R_URL, description.url().toString())
        .set(
          REPOSITORIES.R_CREDENTIALS_TYPE,
          credentialsType(description.credentials()))
        .set(
          REPOSITORIES.R_CREDENTIALS_USERNAME,
          credentialsUsername(description.credentials()))
        .set(
          REPOSITORIES.R_CREDENTIALS_PASSWORD,
          credentialsPassword(description.credentials()))
        .set(
          REPOSITORIES.R_SIGNING_POLICY,
          signingPolicy(description.signingPolicy()));

    recordQuery(query);
    query.execute();

    this.auditEventPut(
      context,
      "REPOSITORY_PUT",
      entry("REPOSITORY", description.id().toString())
    );
    return UNIT;
  }

  private static RepositorySigningPolicyT signingPolicy(
    final NPRepositorySigningPolicy policy)
  {
    return switch (policy) {
      case REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY ->
        RepositorySigningPolicyT.REPOSITORY_REQUIRE_COMMITS_SIGNED_WITH_KNOWN_KEY;
      case ALLOW_UNSIGNED_COMMITS ->
        RepositorySigningPolicyT.REPOSITORY_ALLOW_UNSIGNED_COMMITS;
      case REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS ->
        RepositorySigningPolicyT.REPOSITORY_REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;
    };
  }

  private static String credentialsUsername(
    final NPRepositoryCredentialsType c)
  {
    if (c instanceof NPRepositoryCredentialsNone) {
      return null;
    }
    if (c instanceof final NPRepositoryCredentialsUsernamePassword u) {
      return u.userName();
    }
    throw new IllegalStateException();
  }

  private static String credentialsPassword(
    final NPRepositoryCredentialsType c)
  {
    if (c instanceof NPRepositoryCredentialsNone) {
      return null;
    }
    if (c instanceof final NPRepositoryCredentialsUsernamePassword u) {
      return u.password();
    }
    throw new IllegalStateException();
  }

  private static RepositoryCredentialsTypeT credentialsType(
    final NPRepositoryCredentialsType c)
  {
    if (c instanceof NPRepositoryCredentialsNone) {
      return REPOSITORY_CREDENTIALS_NONE;
    }
    if (c instanceof NPRepositoryCredentialsUsernamePassword) {
      return REPOSITORY_CREDENTIALS_USERNAME_PASSWORD;
    }
    throw new IllegalStateException();
  }
}
