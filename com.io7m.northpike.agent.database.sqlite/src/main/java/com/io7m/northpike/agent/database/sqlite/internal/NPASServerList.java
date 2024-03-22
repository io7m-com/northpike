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
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerListType.Parameters;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.agents.NPAgentServerSummary;
import org.jooq.Condition;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.util.List;

import static com.io7m.northpike.agent.database.sqlite.internal.tables.Servers.SERVERS;

/**
 * Retrieve a server.
 */

public final class NPASServerList
  extends NPASQAbstract<Parameters, List<NPAgentServerSummary>>
  implements NPAgentDatabaseQueriesServersType.ServerListType
{
  private static final Service<Parameters, List<NPAgentServerSummary>, ServerListType> SERVICE =
    new Service<>(ServerListType.class, NPASServerList::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASServerList(
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

  private static NPAgentServerSummary mapRecord(
    final org.jooq.Record r)
  {
    return new NPAgentServerSummary(
      NPAgentServerID.of(r.get(SERVERS.S_ID)),
      r.get(SERVERS.S_REMOTE_ADDRESS)
    );
  }

  @Override
  protected List<NPAgentServerSummary> onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPAgentDatabaseException
  {
    final Condition condition;
    if (parameters.offset().isPresent()) {
      condition = SERVERS.S_ID.gt(parameters.offset().get().toString());
    } else {
      condition = DSL.trueCondition();
    }

    return context.select(
        SERVERS.S_ID,
        SERVERS.S_REMOTE_ADDRESS
      ).from(SERVERS)
      .where(condition)
      .orderBy(SERVERS.S_ID.asc())
      .limit(Long.valueOf(parameters.limit()))
      .stream()
      .map(NPASServerList::mapRecord)
      .toList();
  }
}
