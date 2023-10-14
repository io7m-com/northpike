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

import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerUnassignType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import org.jooq.DSLContext;

import static com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit.UNIT;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.AGENT_SERVERS;
import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;

/**
 * Unassign a server from an agent.
 */

public final class NPASAgentServerUnassign
  extends NPASQAbstract<NPAgentLocalName, NPAgentDatabaseUnit>
  implements AgentServerUnassignType
{
  private static final Service<NPAgentLocalName, NPAgentDatabaseUnit, AgentServerUnassignType> SERVICE =
    new Service<>(AgentServerUnassignType.class, NPASAgentServerUnassign::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentServerUnassign(
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
    final NPAgentLocalName name)
  {
    final var agent =
      context.select(AGENTS.A_ID)
        .from(AGENTS)
        .where(AGENTS.A_NAME.eq(name.toString()));

    final var query =
      context.deleteFrom(AGENT_SERVERS)
        .where(AGENT_SERVERS.AS_AGENT.eq(agent));

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
