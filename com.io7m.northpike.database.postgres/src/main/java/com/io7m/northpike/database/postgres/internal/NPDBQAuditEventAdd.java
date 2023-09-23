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
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import org.jooq.DSLContext;
import org.jooq.Query;
import org.jooq.postgres.extensions.types.Hstore;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.UUID;

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

  private static Query auditEvent(
    final DSLContext context,
    final NPAuditEvent parameters)
  {
    final var set =
      context.insertInto(AUDIT)
        .set(AUDIT.AU_TYPE, parameters.type())
        .set(AUDIT.AU_TIME, parameters.time())
        .set(AU_DATA, Hstore.valueOf(parameters.data()));

    final var owner = parameters.owner();
    if (owner instanceof final NPAuditUserOrAgentType.User user) {
      return set.set(AUDIT.AU_USER, user.id())
        .set(AUDIT.AU_AGENT, (UUID) null);
    }

    if (owner instanceof final NPAuditUserOrAgentType.Agent agent) {
      return set.set(AUDIT.AU_USER, (UUID) null)
        .set(AUDIT.AU_AGENT, agent.id().value());
    }

    throw new IllegalStateException();
  }

  @SafeVarargs
  static Query auditEvent(
    final DSLContext context,
    final OffsetDateTime time,
    final NPAuditUserOrAgentType user,
    final String type,
    final Map.Entry<String, String>... entries)
  {
    return auditEvent(
      context,
      new NPAuditEvent(time, user, type, Map.ofEntries(entries))
    );
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
    final NPAuditEvent parameters)
    throws NPDatabaseException
  {
    auditEvent(context, parameters).execute();
    return NPDatabaseUnit.UNIT;
  }

}
