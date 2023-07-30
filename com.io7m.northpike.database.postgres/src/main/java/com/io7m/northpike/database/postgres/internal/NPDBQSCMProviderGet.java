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
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType.GetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPSCMProviderDescription;
import org.jooq.DSLContext;
import org.jooq.Record4;

import java.net.URI;
import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.tables.ScmProviders.SCM_PROVIDERS;

/**
 * Retrieve an SCM provider.
 */

public final class NPDBQSCMProviderGet
  extends NPDBQAbstract<RDottedName, Optional<NPSCMProviderDescription>>
  implements GetType
{
  private static final Service<RDottedName, Optional<NPSCMProviderDescription>, GetType> SERVICE =
    new Service<>(GetType.class, NPDBQSCMProviderGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQSCMProviderGet(
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
  protected Optional<NPSCMProviderDescription> onExecute(
    final DSLContext context,
    final RDottedName name)
  {
    final var query =
      context.select(
          SCM_PROVIDERS.SP_ID,
          SCM_PROVIDERS.SP_NAME,
          SCM_PROVIDERS.SP_DESCRIPTION,
          SCM_PROVIDERS.SP_URL
        ).from(SCM_PROVIDERS)
        .where(SCM_PROVIDERS.SP_NAME.eq(name.value()));

    recordQuery(query);
    return query.fetchOptional().map(NPDBQSCMProviderGet::mapProvider);
  }

  private static NPSCMProviderDescription mapProvider(
    final Record4<Long, String, String, String> r)
  {
    return new NPSCMProviderDescription(
      new RDottedName(r.get(SCM_PROVIDERS.SP_NAME)),
      r.get(SCM_PROVIDERS.SP_DESCRIPTION),
      URI.create(r.get(SCM_PROVIDERS.SP_URL))
    );
  }
}
