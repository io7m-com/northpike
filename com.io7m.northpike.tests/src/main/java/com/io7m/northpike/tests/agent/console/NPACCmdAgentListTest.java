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


package com.io7m.northpike.tests.agent.console;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseConnectionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentListType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseTransactionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.internal.console.NPACCmdAgentList;
import com.io7m.northpike.agent.internal.console.NPACCommandContextType;
import com.io7m.northpike.agent.internal.status.NPAgentConnectionStatusConnected;
import com.io7m.northpike.agent.internal.status.NPAgentConnectionStatusUnconfigured;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusIdle;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusUnconfigured;
import com.io7m.northpike.agent.internal.status.NPAgentWorkerStatus;
import com.io7m.northpike.agent.internal.supervisor.NPAgentSupervisorType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentStatus;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentList;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.time.Duration;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.agents.NPAgentStatusHealth.HEALTHY;
import static com.io7m.northpike.model.agents.NPAgentStatusHealth.UNHEALTHY;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static java.util.Map.entry;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPACCmdAgentListTest
{
  private NPACCommandContextType context;
  private RPServiceDirectory services;
  private NPStrings strings;
  private NPAgentDatabaseType database;
  private NPAgentDatabaseTransactionType transaction;
  private NPAgentDatabaseConnectionType connection;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.context =
      Mockito.mock(NPACCommandContextType.class);
    this.strings =
      NPStrings.create(Locale.ROOT);
    this.database =
      Mockito.mock(NPAgentDatabaseType.class);
    this.transaction =
      Mockito.mock(NPAgentDatabaseTransactionType.class);
    this.connection =
      Mockito.mock(NPAgentDatabaseConnectionType.class);

    Mockito.when(this.database.openConnection())
      .thenReturn(this.connection);
    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);

    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, this.strings);
    this.services.register(NPAgentDatabaseType.class, this.database);

    Mockito.when(this.context.services())
      .thenReturn(this.services);

    Mockito.doAnswer(invocationOnMock -> {
      final var message =
        invocationOnMock.getArgument(0, NPStringConstantType.class);
      final var errorCode =
        invocationOnMock.getArgument(1, NPErrorCode.class);

      return new NPException(
        message.toString(),
        errorCode,
        Map.of(),
        Optional.empty()
      );
    }).when(this.context).fail(any(), any());
  }

  /**
   * Requires authentication.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure0()
    throws Exception
  {
    final var handler = new NPACCmdAgentList();

    Mockito.doThrow(new NPException(
      ERROR_AUTHENTICATION.name(),
      errorAuthentication(),
      Map.of(),
      Optional.empty()
    )).when(this.context).onAuthenticationRequire();

    final var command =
      new NPACCommandAgentList(
        UUID.randomUUID()
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Succeeds if permitted.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPACCmdAgentList();

    final var command =
      new NPACCommandAgentList(
        UUID.randomUUID()
      );

    final var supervisor =
      Mockito.mock(NPAgentSupervisorType.class);

    this.services.register(NPAgentSupervisorType.class, supervisor);

    final var query =
      Mockito.mock(AgentListType.class);
    Mockito.when(this.transaction.queries(AgentListType.class))
      .thenReturn(query);
    Mockito.when(query.execute(any()))
      .thenReturn(List.of(NPAgentLocalName.of("d")));

    final Map<NPAgentLocalName, NPAgentStatus> results =
      Map.ofEntries(
        entry(
          NPAgentLocalName.of("a"),
          new NPAgentStatus(
            HEALTHY,
            "Connected to example.com (Latency PT0S). Work executor is ready.")
        ),
        entry(
          NPAgentLocalName.of("b"),
          new NPAgentStatus(
            UNHEALTHY,
            "No server configured. Work executor is ready.")
        ),
        entry(
          NPAgentLocalName.of("c"),
          new NPAgentStatus(
            UNHEALTHY,
            "Connected to example.com (Latency PT0S). No work executor configured.")
        ),
        entry(
          NPAgentLocalName.of("d"),
          new NPAgentStatus(
            UNHEALTHY,
            "No server configured. No work executor configured.")
        )
      );

    final Map<NPAgentLocalName, NPAgentWorkerStatus> supervisorResults =
      Map.ofEntries(
        entry(
          NPAgentLocalName.of("a"),
          new NPAgentWorkerStatus(
            new NPAgentConnectionStatusConnected("example.com", Duration.ZERO),
            new NPAgentWorkExecutorStatusIdle()
          )
        ),
        entry(
          NPAgentLocalName.of("b"),
          new NPAgentWorkerStatus(
            new NPAgentConnectionStatusUnconfigured(),
            new NPAgentWorkExecutorStatusIdle()
          )
        ),
        entry(
          NPAgentLocalName.of("c"),
          new NPAgentWorkerStatus(
            new NPAgentConnectionStatusConnected("example.com", Duration.ZERO),
            new NPAgentWorkExecutorStatusUnconfigured()
          )
        )
      );


    Mockito.when(supervisor.agentStatuses())
      .thenReturn(supervisorResults);

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());
    assertEquals(results, r.results());
  }
}
