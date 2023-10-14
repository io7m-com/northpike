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
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import org.jooq.DSLContext;

import static com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit.UNIT;
import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;

/**
 * Update an agent.
 */

public final class NPASAgentPut
  extends NPASQAbstract<NPAgentLocalDescription, NPAgentDatabaseUnit>
  implements NPAgentDatabaseQueriesAgentsType.AgentPutType
{
  private static final Service<NPAgentLocalDescription, NPAgentDatabaseUnit, AgentPutType> SERVICE =
    new Service<>(AgentPutType.class, NPASAgentPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentPut(
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
    final NPAgentLocalDescription agent)
  {
    final var keyPair = agent.keyPair();

    final var query =
      context.insertInto(AGENTS)
        .set(AGENTS.A_NAME, agent.name().toString())
        .set(AGENTS.A_KEY_ALGO, keyPair.algorithm())
        .set(AGENTS.A_KEY_PUBLIC, keyPair.publicKey().asText())
        .set(AGENTS.A_KEY_PRIVATE, keyPair.privateKey().asText())
        .onDuplicateKeyUpdate()
        .set(AGENTS.A_NAME, agent.name().toString())
        .set(AGENTS.A_KEY_ALGO, keyPair.algorithm())
        .set(AGENTS.A_KEY_PUBLIC, keyPair.publicKey().asText())
        .set(AGENTS.A_KEY_PRIVATE, keyPair.privateKey().asText());

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
