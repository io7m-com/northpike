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
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseTransactionType;
import com.io7m.northpike.agent.internal.console.NPACCmdAgentCreate;
import com.io7m.northpike.agent.internal.console.NPACCommandContextType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentCreate;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.Times;

import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorDuplicate;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;

/**
 * Tests for a command.
 */

public final class NPACCmdAgentCreateTest
{
  private NPACCommandContextType context;
  private NPAgentDatabaseConnectionType connection;
  private NPAgentDatabaseTransactionType transaction;
  private RPServiceDirectory services;
  private NPStrings strings;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.context =
      Mockito.mock(NPACCommandContextType.class);

    this.strings = NPStrings.create(Locale.ROOT);
    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, this.strings);

    this.connection =
      Mockito.mock(NPAgentDatabaseConnectionType.class);
    this.transaction =
      Mockito.mock(NPAgentDatabaseTransactionType.class);

    Mockito.when(this.context.databaseConnection())
      .thenReturn(this.connection);
    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);

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
    final var handler = new NPACCmdAgentCreate();

    Mockito.doThrow(new NPException(
      ERROR_AUTHENTICATION.name(),
      errorAuthentication(),
      Map.of(),
      Optional.empty()
    )).when(this.context).onAuthenticationRequire();

    final var command =
      new NPACCommandAgentCreate(
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
    final var handler = new NPACCmdAgentCreate();

    final var command =
      new NPACCommandAgentCreate(
        UUID.randomUUID(),
        NPAgentLocalName.of("a")
      );

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    final var agentPut =
      Mockito.mock(AgentPutType.class);

    Mockito.when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);
    Mockito.when(this.transaction.queries(AgentPutType.class))
      .thenReturn(agentPut);

    Mockito.when(agentGet.execute(any()))
      .thenReturn(Optional.empty());

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    Mockito.verify(agentGet, new Times(1))
      .execute(eq(NPAgentLocalName.of("a")));
    Mockito.verify(agentPut, new Times(1))
      .execute(any());
  }

  /**
   * Fails if agent exists.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailExists()
    throws Exception
  {
    final var handler = new NPACCmdAgentCreate();

    final var command =
      new NPACCommandAgentCreate(
        UUID.randomUUID(),
        NPAgentLocalName.of("a")
      );

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    final var agentPut =
      Mockito.mock(AgentPutType.class);

    Mockito.when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);
    Mockito.when(this.transaction.queries(AgentPutType.class))
      .thenReturn(agentPut);

    Mockito.when(agentGet.execute(any()))
      .thenReturn(Optional.of(
        new NPAgentLocalDescription(
          NPAgentLocalName.of("a"),
          new NPAgentKeyPairFactoryEd448().generateKeyPair()
        )
      ));

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals(errorDuplicate(), ex.errorCode());

    Mockito.verify(agentGet, new Times(1))
      .execute(eq(NPAgentLocalName.of("a")));

    Mockito.verifyNoInteractions(agentPut);
  }
}
