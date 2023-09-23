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
import com.io7m.northpike.database.api.NPDatabaseQueriesAuditType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPAuditEvent;
import org.jooq.DSLContext;
import org.jooq.postgres.extensions.types.Hstore;

import static com.io7m.northpike.database.postgres.internal.NPDBQAuditEventSearch.AU_DATA;
import static com.io7m.northpike.database.postgres.internal.tables.Audit.AUDIT;

/**
 * Add audit events.
 */

public final class NPDBQAuditEventAdd
  extends NPDBQAbstract<NPAuditEvent, NPDatabaseUnit>
  implements NPDatabaseQueriesAuditType.EventAddType
{
  private static final Service<NPAuditEvent, NPDatabaseUnit, EventAddType> SERVICE =
    new Service<>(EventAddType.class, NPDBQAuditEventAdd::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAuditEventAdd(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPAuditEvent parameters)
    throws NPDatabaseException
  {
    context.insertInto(AUDIT)
      .set(AUDIT.AU_TYPE, parameters.type())
      .set(AUDIT.AU_USER, parameters.user())
      .set(AUDIT.AU_TIME, parameters.time())
      .set(AU_DATA, Hstore.valueOf(parameters.data()))
      .execute();
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
