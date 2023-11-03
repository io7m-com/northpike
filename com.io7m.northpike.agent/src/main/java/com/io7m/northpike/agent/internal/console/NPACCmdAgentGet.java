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


package com.io7m.northpike.agent.internal.console;


import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentWorkExecGetType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentGet;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;

import java.util.UUID;

/**
 * @see NPACCommandAgentGet
 */

public final class NPACCmdAgentGet
  extends NPACCmdAbstract<NPACResponseAgent, NPACCommandAgentGet>
{
  /**
   * @see NPACCommandAgentGet
   */

  public NPACCmdAgentGet()
  {
    super(NPACCommandAgentGet.class);
  }

  @Override
  public NPACResponseAgent execute(
    final NPACCommandContextType context,
    final NPACCommandAgentGet command)
    throws NPException
  {
    context.onAuthenticationRequire();

    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var existing =
          transaction.queries(AgentGetType.class)
            .execute(command.name());
        final var server =
          transaction.queries(AgentServerGetType.class)
            .execute(command.name());
        final var workExec =
          transaction.queries(AgentWorkExecGetType.class)
            .execute(command.name());

        return new NPACResponseAgent(
          UUID.randomUUID(),
          command.messageID(),
          existing.map(x -> {
            return new NPACResponseAgent.Result(
              x.name(),
              x.keyPair().publicKey(),
              server,
              workExec
            );
          })
        );
      }
    }
  }
}
