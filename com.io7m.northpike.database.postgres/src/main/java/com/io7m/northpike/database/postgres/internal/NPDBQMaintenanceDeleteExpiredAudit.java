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

import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType.DeleteExpiredAuditType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;

import java.time.OffsetDateTime;

import static com.io7m.northpike.database.postgres.internal.Tables.AUDIT;

/**
 * A query to run maintenance.
 */

public final class NPDBQMaintenanceDeleteExpiredAudit
  extends NPDBQAbstract<OffsetDateTime, Long>
  implements DeleteExpiredAuditType
{
  private static final Service<OffsetDateTime, Long, DeleteExpiredAuditType> SERVICE =
    new Service<>(
      DeleteExpiredAuditType.class,
      NPDBQMaintenanceDeleteExpiredAudit::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQMaintenanceDeleteExpiredAudit(
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
  protected Long onExecute(
    final DSLContext context,
    final OffsetDateTime parameters)
  {
    return Long.valueOf(
      (long) context.deleteFrom(AUDIT)
        .where(AUDIT.AU_TIME.lt(parameters))
        .execute()
    );
  }
}
