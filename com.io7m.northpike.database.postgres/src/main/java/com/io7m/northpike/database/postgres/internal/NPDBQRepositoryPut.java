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
import com.io7m.northpike.model.NPRepository;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.tables.Repositories.REPOSITORIES;
import static com.io7m.northpike.database.postgres.internal.tables.ScmProviders.SCM_PROVIDERS;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;
import static com.io7m.northpike.strings.NPStringConstants.SCM_PROVIDER;

/**
 * Update a repository.
 */

public final class NPDBQRepositoryPut
  extends NPDBQAbstract<NPRepository, NPDatabaseUnit>
  implements NPDatabaseQueriesRepositoriesType.PutType
{
  private static final Service<NPRepository, NPDatabaseUnit, PutType> SERVICE =
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
    final NPRepository description)
  {
    this.setAttribute(SCM_PROVIDER, description.provider().value());
    this.setAttribute(REPOSITORY, description.url().toString());

    final var selectedProvider =
      context.select(SCM_PROVIDERS.SP_ID)
        .from(SCM_PROVIDERS)
        .where(SCM_PROVIDERS.SP_NAME.eq(description.provider().value()));

    final var query =
      context.insertInto(REPOSITORIES)
        .set(REPOSITORIES.R_ID, description.id())
        .set(REPOSITORIES.R_PASSWORD, description.password().orElse(null))
        .set(REPOSITORIES.R_PROVIDER, selectedProvider)
        .set(REPOSITORIES.R_URL, description.url().toString())
        .set(REPOSITORIES.R_USER, description.userName().orElse(null))
        .onConflict(REPOSITORIES.R_URL)
        .doUpdate()
        .set(REPOSITORIES.R_ID, description.id())
        .set(REPOSITORIES.R_PASSWORD, description.password().orElse(null))
        .set(REPOSITORIES.R_PROVIDER, selectedProvider)
        .set(REPOSITORIES.R_URL, description.url().toString())
        .set(REPOSITORIES.R_USER, description.userName().orElse(null));

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
