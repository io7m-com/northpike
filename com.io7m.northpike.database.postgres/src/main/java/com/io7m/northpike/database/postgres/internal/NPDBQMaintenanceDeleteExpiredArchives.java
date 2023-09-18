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

import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredArchivesType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPToken;
import org.jooq.DSLContext;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.OffsetDateTime;
import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.northpike.database.postgres.internal.Tables.ARCHIVES;

/**
 * A query to run maintenance.
 */

public final class NPDBQMaintenanceDeleteExpiredArchives
  extends NPDBQAbstract<OffsetDateTime, Set<NPToken>>
  implements DeleteExpiredArchivesType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDBQMaintenanceDeleteExpiredArchives.class);

  private static final Service<OffsetDateTime, Set<NPToken>, DeleteExpiredArchivesType> SERVICE =
    new Service<>(
      DeleteExpiredArchivesType.class,
      NPDBQMaintenanceDeleteExpiredArchives::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQMaintenanceDeleteExpiredArchives(
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
  protected Set<NPToken> onExecute(
    final DSLContext context,
    final OffsetDateTime parameters)
  {
    return context.deleteFrom(ARCHIVES)
      .where(ARCHIVES.AR_CREATED.lt(parameters))
      .returning(ARCHIVES.AR_TOKEN)
      .stream()
      .map(r -> new NPToken(r.get(ARCHIVES.AR_TOKEN)))
      .collect(Collectors.toUnmodifiableSet());
  }
}
