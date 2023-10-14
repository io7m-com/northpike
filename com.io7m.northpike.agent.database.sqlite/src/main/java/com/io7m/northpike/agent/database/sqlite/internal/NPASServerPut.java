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

import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import org.jooq.DSLContext;

import static com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit.UNIT;
import static com.io7m.northpike.agent.database.sqlite.internal.Tables.SERVERS;

/**
 * Update a server.
 */

public final class NPASServerPut
  extends NPASQAbstract<NPAgentServerDescription, NPAgentDatabaseUnit>
  implements NPAgentDatabaseQueriesServersType.ServerPutType
{
  private static final Service<NPAgentServerDescription, NPAgentDatabaseUnit, ServerPutType> SERVICE =
    new Service<>(ServerPutType.class, NPASServerPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASServerPut(
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
    final NPAgentServerDescription server)
  {
    final var query =
      context.insertInto(SERVERS)
        .set(SERVERS.S_ID,
             server.id().toString())
        .set(SERVERS.S_REMOTE_ADDRESS,
             server.hostname())
        .set(SERVERS.S_PORT,
             Integer.valueOf(server.port()))
        .set(SERVERS.S_TLS,
             Integer.valueOf(server.useTLS() ? 1 : 0))
        .set(SERVERS.S_MESSAGE_SIZE_LIMIT,
             Integer.valueOf(server.messageSizeLimit()))
        .onDuplicateKeyUpdate()
        .set(SERVERS.S_ID,
             server.id().toString())
        .set(SERVERS.S_REMOTE_ADDRESS,
             server.hostname())
        .set(SERVERS.S_PORT,
             Integer.valueOf(server.port()))
        .set(SERVERS.S_TLS,
             Integer.valueOf(server.useTLS() ? 1 : 0))
        .set(SERVERS.S_MESSAGE_SIZE_LIMIT,
             Integer.valueOf(server.messageSizeLimit()));

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
