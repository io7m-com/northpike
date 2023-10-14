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
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import org.jooq.DSLContext;

import java.util.Optional;

import static com.io7m.northpike.agent.database.sqlite.internal.tables.Servers.SERVERS;

/**
 * Retrieve a server.
 */

public final class NPASServerGet
  extends NPASQAbstract<NPAgentServerID, Optional<NPAgentServerDescription>>
  implements NPAgentDatabaseQueriesServersType.ServerGetType
{
  private static final Service<NPAgentServerID, Optional<NPAgentServerDescription>, ServerGetType> SERVICE =
    new Service<>(ServerGetType.class, NPASServerGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASServerGet(
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
  protected Optional<NPAgentServerDescription> onExecute(
    final DSLContext context,
    final NPAgentServerID server)
  {
    final var result =
      context.select(
          SERVERS.S_ID,
          SERVERS.S_REMOTE_ADDRESS,
          SERVERS.S_PORT,
          SERVERS.S_TLS,
          SERVERS.S_MESSAGE_SIZE_LIMIT
        ).from(SERVERS)
        .where(SERVERS.S_ID.eq(server.toString()))
        .fetchOptional();

    return result.map(NPASServerGet::mapRecord);
  }

  private static NPAgentServerDescription mapRecord(
    final org.jooq.Record record)
  {
    return new NPAgentServerDescription(
      NPAgentServerID.of(record.get(SERVERS.S_ID)),
      record.get(SERVERS.S_REMOTE_ADDRESS),
      record.<Integer>get(SERVERS.S_PORT).intValue(),
      record.<Integer>get(SERVERS.S_TLS).intValue() == 1,
      record.<Integer>get(SERVERS.S_MESSAGE_SIZE_LIMIT).intValue()
    );
  }
}
