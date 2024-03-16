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

import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentListType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentListType.Parameters;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.internal.status.NPAgentConnectionStatusUnconfigured;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusUnconfigured;
import com.io7m.northpike.agent.internal.status.NPAgentWorkerStatus;
import com.io7m.northpike.agent.internal.supervisor.NPAgentSupervisorType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentStatus;
import com.io7m.northpike.model.agents.NPAgentStatusHealth;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentCreate;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentList;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgentList;
import com.io7m.northpike.strings.NPStrings;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;
import java.util.stream.Collectors;

/**
 * @see NPACCommandAgentList
 */

public final class NPACCmdAgentList
  extends NPACCmdAbstract<NPACResponseAgentList, NPACCommandAgentList>
{
  /**
   * @see NPACCommandAgentCreate
   */

  public NPACCmdAgentList()
  {
    super(NPACCommandAgentList.class);
  }

  @Override
  public NPACResponseAgentList execute(
    final NPACCommandContextType context,
    final NPACCommandAgentList command)
    throws NPException
  {
    context.onAuthenticationRequire();

    final var services =
      context.services();
    final var supervisor =
      services.requireService(NPAgentSupervisorType.class);
    final var strings =
      services.requireService(NPStrings.class);
    final var database =
      services.requireService(NPAgentDatabaseType.class);

    final var workers =
      new HashMap<>(supervisor.agentStatuses());

    try (var connection = database.openConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var query =
          transaction.queries(AgentListType.class);
        final var agents =
          query.execute(new Parameters(Optional.empty(), 0L));

        for (final var agent : agents) {
          if (!workers.containsKey(agent)) {
            workers.put(
              agent,
              new NPAgentWorkerStatus(
                new NPAgentConnectionStatusUnconfigured(),
                new NPAgentWorkExecutorStatusUnconfigured())
            );
          }
        }
      }
    }

    return new NPACResponseAgentList(
      UUID.randomUUID(),
      command.messageID(),
      workers.entrySet()
        .stream()
        .map(e -> mapEntry(strings, e))
        .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue))
    );
  }

  private static Map.Entry<NPAgentLocalName, NPAgentStatus> mapEntry(
    final NPStrings strings,
    final Map.Entry<NPAgentLocalName, NPAgentWorkerStatus> e)
  {
    return Map.entry(e.getKey(), mapStatus(strings, e.getValue()));
  }

  private static NPAgentStatus mapStatus(
    final NPStrings strings,
    final NPAgentWorkerStatus status)
  {
    return new NPAgentStatus(
      mapHealth(status.health()),
      status.format(strings)
    );
  }

  private static NPAgentStatusHealth mapHealth(
    final NPAgentStatusHealth health)
  {
    return switch (health) {
      case HEALTHY -> NPAgentStatusHealth.HEALTHY;
      case UNHEALTHY -> NPAgentStatusHealth.UNHEALTHY;
    };
  }
}
