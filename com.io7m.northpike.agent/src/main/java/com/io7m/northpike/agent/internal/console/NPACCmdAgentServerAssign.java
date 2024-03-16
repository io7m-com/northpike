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


import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerAssignType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerAssignType.Parameters;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerUnassignType;
import com.io7m.northpike.agent.internal.events.NPAgentServerAssigned;
import com.io7m.northpike.agent.internal.events.NPAgentServerUnassigned;
import com.io7m.northpike.agent.internal.events.NPAgentUpdated;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentServerAssign;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;

/**
 * @see NPACCommandAgentGet
 */

public final class NPACCmdAgentServerAssign
  extends NPACCmdAbstract<NPACResponseOK, NPACCommandAgentServerAssign>
{
  /**
   * @see NPACCommandAgentGet
   */

  public NPACCmdAgentServerAssign()
  {
    super(NPACCommandAgentServerAssign.class);
  }

  @Override
  public NPACResponseOK execute(
    final NPACCommandContextType context,
    final NPACCommandAgentServerAssign command)
    throws NPException
  {
    context.onAuthenticationRequire();

    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {

        final var serverOpt = command.server();
        final var agentName = command.name();
        if (serverOpt.isPresent()) {
          transaction.queries(AgentServerAssignType.class)
            .execute(new Parameters(agentName, serverOpt.get()));
        } else {
          transaction.queries(AgentServerUnassignType.class)
            .execute(agentName);
        }

        transaction.commit();

        if (serverOpt.isPresent()) {
          final var server = serverOpt.get();
          context.publishEvent(new NPAgentServerAssigned(agentName, server));
        } else {
          context.publishEvent(new NPAgentServerUnassigned(agentName));
        }
        context.publishEvent(new NPAgentUpdated(agentName));
        return NPACResponseOK.createCorrelated(command);
      }
    }
  }
}
