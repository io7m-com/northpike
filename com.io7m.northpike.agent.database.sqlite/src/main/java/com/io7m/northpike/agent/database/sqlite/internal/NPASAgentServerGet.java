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

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;
import org.jooq.DSLContext;

import java.util.Optional;

import static com.io7m.northpike.agent.database.sqlite.internal.Tables.AGENT_SERVERS;
import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;

/**
 * Retrieve the server associated with the given agent, if any.
 */

public final class NPASAgentServerGet
  extends NPASQAbstract<NPAgentLocalName, Optional<NPAgentServerID>>
  implements NPAgentDatabaseQueriesAgentsType.AgentServerGetType
{
  private static final Service<NPAgentLocalName, Optional<NPAgentServerID>, AgentServerGetType> SERVICE =
    new Service<>(AgentServerGetType.class, NPASAgentServerGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentServerGet(
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
  protected Optional<NPAgentServerID> onExecute(
    final DSLContext context,
    final NPAgentLocalName agentName)
    throws NPAgentDatabaseException
  {
    return context.select(AGENT_SERVERS.AS_SERVER)
      .from(AGENT_SERVERS)
      .join(AGENTS)
      .on(AGENTS.A_ID.eq(AGENT_SERVERS.AS_AGENT))
      .fetchOptional()
      .map(r -> NPAgentServerID.of(r.get(AGENT_SERVERS.AS_SERVER)));
  }
}
