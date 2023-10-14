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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import org.jooq.DSLContext;
import org.jooq.Query;

import java.util.ArrayList;

import static com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit.UNIT;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.AGENT_SERVERS;
import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;

/**
 * Delete an agent.
 */

public final class NPASAgentDelete
  extends NPASQAbstract<NPAgentLocalName, NPAgentDatabaseUnit>
  implements NPAgentDatabaseQueriesAgentsType.AgentDeleteType
{
  private static final Service<NPAgentLocalName, NPAgentDatabaseUnit, AgentDeleteType> SERVICE =
    new Service<>(AgentDeleteType.class, NPASAgentDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentDelete(
    final NPASTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPASQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected NPAgentDatabaseUnit onExecute(
    final DSLContext context,
    final NPAgentLocalName agent)
  {
    final var batch = new ArrayList<Query>();

    batch.add(
      context.deleteFrom(AGENT_SERVERS)
        .where(AGENT_SERVERS.AS_AGENT.eq(
          context.select(AGENTS.A_ID)
            .from(AGENTS)
            .where(AGENTS.A_NAME.eq(agent.toString()))
        ))
    );

    batch.add(
      context.deleteFrom(AGENTS)
        .where(AGENTS.A_NAME.eq(agent.toString()))
    );

    context.batch(batch).execute();
    return UNIT;
  }
}
