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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseConnectionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentWorkExecGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseTransactionType;
import com.io7m.northpike.agent.internal.console.NPACCmdAgentGet;
import com.io7m.northpike.agent.internal.console.NPACCommandContextType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentGet;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;
import com.io7m.northpike.strings.NPStringConstantType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.nio.file.Paths;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPACCmdAgentGetTest
{
  private NPACCommandContextType context;
  private NPAgentDatabaseConnectionType connection;
  private NPAgentDatabaseTransactionType transaction;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.context =
      Mockito.mock(NPACCommandContextType.class);

    this.connection =
      Mockito.mock(NPAgentDatabaseConnectionType.class);
    this.transaction =
      Mockito.mock(NPAgentDatabaseTransactionType.class);

    Mockito.when(this.context.databaseConnection())
      .thenReturn(this.connection);
    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);

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
    final var handler = new NPACCmdAgentGet();

    Mockito.doThrow(new NPException(
      ERROR_AUTHENTICATION.name(),
      errorAuthentication(),
      Map.of(),
      Optional.empty()
    )).when(this.context).onAuthenticationRequire();

    final var command =
      new NPACCommandAgentGet(
        UUID.randomUUID(),
        NPAgentLocalName.of("a")
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
    final var handler = new NPACCmdAgentGet();

    final var command =
      new NPACCommandAgentGet(
        UUID.randomUUID(),
        NPAgentLocalName.of("a")
      );

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    final var agentServerGet =
      Mockito.mock(AgentServerGetType.class);
    final var agentWorkExecGet =
      Mockito.mock(AgentWorkExecGetType.class);

    Mockito.when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);
    Mockito.when(this.transaction.queries(AgentServerGetType.class))
      .thenReturn(agentServerGet);
    Mockito.when(this.transaction.queries(AgentWorkExecGetType.class))
      .thenReturn(agentWorkExecGet);

    Mockito.when(agentGet.execute(any()))
      .thenReturn(Optional.empty());
    Mockito.when(agentServerGet.execute(any()))
      .thenReturn(Optional.empty());
    Mockito.when(agentWorkExecGet.execute(any()))
      .thenReturn(Optional.empty());

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    assertEquals(Optional.empty(), r.results());
  }

  /**
   * Succeeds if permitted.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess1()
    throws Exception
  {
    final var handler = new NPACCmdAgentGet();

    final var command =
      new NPACCommandAgentGet(
        UUID.randomUUID(),
        NPAgentLocalName.of("a")
      );

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    final var agentServerGet =
      Mockito.mock(AgentServerGetType.class);
    final var agentWorkExecGet =
      Mockito.mock(AgentWorkExecGetType.class);

    Mockito.when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);
    Mockito.when(this.transaction.queries(AgentServerGetType.class))
      .thenReturn(agentServerGet);
    Mockito.when(this.transaction.queries(AgentWorkExecGetType.class))
      .thenReturn(agentWorkExecGet);

    final var agent0 =
      new NPAgentLocalDescription(
        NPAgentLocalName.of("a"),
        new NPAgentKeyPairFactoryEd448().generateKeyPair()
      );
    final var serverId =
      new NPAgentServerID(UUID.randomUUID());
    final var workExec =
      NPAWorkExecutorConfiguration.builder()
        .setExecutorType(new RDottedName("a"))
        .setWorkDirectory(Paths.get("a"))
        .setTemporaryDirectory(Paths.get("b"))
        .build();

    Mockito.when(agentGet.execute(any()))
      .thenReturn(Optional.of(agent0));
    Mockito.when(agentServerGet.execute(any()))
      .thenReturn(Optional.of(serverId));
    Mockito.when(agentWorkExecGet.execute(any()))
      .thenReturn(Optional.of(workExec));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    assertEquals(Optional.of(
      new NPACResponseAgent.Result(
        agent0.name(),
        agent0.keyPair().publicKey(),
        Optional.of(serverId),
        Optional.of(workExec)
      )
    ), r.results());
  }
}
