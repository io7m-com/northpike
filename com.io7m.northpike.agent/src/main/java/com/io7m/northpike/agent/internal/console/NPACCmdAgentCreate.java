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
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.agent.internal.events.NPAgentUpdated;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentCreate;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.strings.NPStrings;

import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorDuplicate;
import static com.io7m.northpike.strings.NPStringConstants.AGENT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_DUPLICATE;
import static java.util.Map.entry;

/**
 * @see NPACCommandAgentCreate
 */

public final class NPACCmdAgentCreate
  extends NPACCmdAbstract<NPACResponseOK, NPACCommandAgentCreate>
{
  /**
   * @see NPACCommandAgentCreate
   */

  public NPACCmdAgentCreate()
  {
    super(NPACCommandAgentCreate.class);
  }

  @Override
  public NPACResponseOK execute(
    final NPACCommandContextType context,
    final NPACCommandAgentCreate command)
    throws NPException
  {
    context.onAuthenticationRequire();

    final var services =
      context.services();
    final var strings =
      services.requireService(NPStrings.class);

    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var agentName =
          command.name();
        final var existing =
          transaction.queries(AgentGetType.class)
            .execute(agentName);

        if (existing.isPresent()) {
          throw new NPException(
            strings.format(ERROR_DUPLICATE),
            errorDuplicate(),
            Map.ofEntries(
              entry(strings.format(AGENT), agentName.toString())
            ),
            Optional.empty()
          );
        }

        final var keyPair =
          new NPAgentKeyPairFactoryEd448()
            .generateKeyPair();

        transaction.queries(AgentPutType.class)
          .execute(new NPAgentLocalDescription(agentName, keyPair));

        transaction.commit();

        context.publishEvent(new NPAgentUpdated(agentName));
        return NPACResponseOK.createCorrelated(command);
      }
    }
  }
}
