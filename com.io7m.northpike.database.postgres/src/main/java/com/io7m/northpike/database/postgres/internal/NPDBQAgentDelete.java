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
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.DeleteType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPAgentID;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.postgres.internal.tables.Agents.AGENTS;
import static java.util.Map.entry;

/**
 * Retrieve an agent.
 */

public final class NPDBQAgentDelete
  extends NPDBQAbstract<NPAgentID, NPDatabaseUnit>
  implements DeleteType
{
  private static final Service<NPAgentID, NPDatabaseUnit, DeleteType> SERVICE =
    new Service<>(DeleteType.class, NPDBQAgentDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentDelete(
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
    final NPAgentID id)
    throws NPDatabaseException
  {
    final var updated =
      context.update(AGENTS)
        .set(AGENTS.A_DELETED, Boolean.TRUE)
        .set(AGENTS.A_ACCESS_KEY, (String) null)
        .where(AGENTS.A_ID.eq(id.value()))
        .execute();

    if (updated > 0) {
      this.auditEventPut(
        context,
        "AGENT_DELETED",
        entry("AGENT", id.value().toString())
      );
    }

    return NPDatabaseUnit.UNIT;
  }
}
