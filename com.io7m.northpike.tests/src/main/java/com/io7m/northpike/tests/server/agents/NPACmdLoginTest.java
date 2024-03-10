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


package com.io7m.northpike.tests.server.agents;

import com.io7m.northpike.clock.NPClock;
import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.LoginChallengeGetForKeyType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.LoginChallengePutType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.server.internal.agents.NPACmdLogin;
import com.io7m.northpike.server.internal.agents.NPAgentCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.tests.plans.NPFakeClock;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.Times;

import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPACmdLoginTest
{
  private NPAgentCommandContextType context;
  private RPServiceDirectory services;
  private NPFakeClock clock;
  private NPClock clockService;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private LoginChallengePutType challengePut;
  private LoginChallengeGetForKeyType challengeGetForKey;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.context =
      Mockito.mock(NPAgentCommandContextType.class);
    this.services =
      new RPServiceDirectory();
    this.clock =
      new NPFakeClock();
    this.clockService =
      new NPClock(this.clock);
    this.connection =
      Mockito.mock(NPDatabaseConnectionType.class);
    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);
    this.challengePut =
      Mockito.mock(LoginChallengePutType.class);
    this.challengeGetForKey =
      Mockito.mock(LoginChallengeGetForKeyType.class);

    this.services.register(NPClockServiceType.class, this.clockService);

    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);
    Mockito.when(this.context.services())
      .thenReturn(this.services);
    Mockito.when(this.context.sourceAddress())
      .thenReturn("www.example.com");
    Mockito.when(this.context.databaseConnection())
      .thenReturn(this.connection);
    Mockito.when(this.transaction.queries(LoginChallengePutType.class))
      .thenReturn(this.challengePut);
    Mockito.when(this.transaction.queries(LoginChallengeGetForKeyType.class))
      .thenReturn(this.challengeGetForKey);

    Mockito.when(this.challengeGetForKey.execute(any()))
        .thenReturn(Optional.empty());

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
   * Fails if no agent exists with the given key.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure0()
    throws Exception
  {
    final var handler = new NPACmdLogin();

    final var command =
      new NPACommandCLogin(
        UUID.randomUUID(),
        new NPAgentKeyPairFactoryEd448().generateKeyPair().publicKey()
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());

    Mockito.verify(this.challengePut, new Times(1))
      .execute(any());
    Mockito.verifyNoMoreInteractions(this.challengePut);
  }

  /**
   * Succeeds if an agent exists with the given key.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPACmdLogin();

    final var key =
      new NPAgentKeyPairFactoryEd448().generateKeyPair().publicKey();
    final var command =
      new NPACommandCLogin(UUID.randomUUID(), key);

    Mockito.when(this.context.agentFindForKey(command.key()))
      .thenReturn(Optional.of(
        new NPAgentDescription(
          NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
          "Agent",
          key,
          Map.of(),
          Map.of(),
          Map.of()
        )
      ));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    Mockito.verify(this.challengePut, new Times(1))
      .execute(any());
    Mockito.verifyNoMoreInteractions(this.challengePut);
  }
}
