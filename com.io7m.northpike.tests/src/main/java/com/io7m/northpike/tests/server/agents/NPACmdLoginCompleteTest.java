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
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeDeleteType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeGetType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeCompletion;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
import com.io7m.northpike.server.internal.agents.NPACmdLoginComplete;
import com.io7m.northpike.server.internal.agents.NPAgentCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.tests.plans.NPFakeClock;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.Times;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPACmdLoginCompleteTest
{
  private NPAgentCommandContextType context;
  private RPServiceDirectory services;
  private NPFakeClock clock;
  private NPClock clockService;
  private NPDatabaseTransactionType transaction;
  private AgentLoginChallengeGetType challengeGet;
  private AgentLoginChallengeDeleteType challengeDelete;

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
    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);
    this.challengeGet =
      Mockito.mock(AgentLoginChallengeGetType.class);
    this.challengeDelete =
      Mockito.mock(AgentLoginChallengeDeleteType.class);

    this.services.register(NPClockServiceType.class, this.clockService);

    Mockito.when(this.context.transaction())
      .thenReturn(this.transaction);
    Mockito.when(this.context.transaction(any()))
      .thenReturn(this.transaction);
    Mockito.when(this.context.services())
      .thenReturn(this.services);
    Mockito.when(this.context.sourceAddress())
      .thenReturn("www.example.com");
    Mockito.when(this.transaction.queries(AgentLoginChallengeGetType.class))
      .thenReturn(this.challengeGet);
    Mockito.when(this.transaction.queries(AgentLoginChallengeDeleteType.class))
      .thenReturn(this.challengeDelete);

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
   * Fails if no challenge exists.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure0()
    throws Exception
  {
    final var handler = new NPACmdLoginComplete();

    final var command =
      new NPACommandCLoginComplete(
        UUID.randomUUID(),
        new NPAgentLoginChallengeCompletion(
          UUID.randomUUID(),
          new byte[0]
        )
      );

    Mockito.when(this.challengeGet.execute(any()))
      .thenReturn(Optional.empty());

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());

    Mockito.verify(this.challengeGet, new Times(1))
      .execute(command.completion().id());

    Mockito.verifyNoMoreInteractions(this.challengeGet);
    Mockito.verifyNoMoreInteractions(this.challengeDelete);
  }

  /**
   * Fails if no agent exists with the given key.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPACmdLoginComplete();

    final var command =
      new NPACommandCLoginComplete(
        UUID.randomUUID(),
        new NPAgentLoginChallengeCompletion(
          UUID.randomUUID(),
          new byte[0]
        )
      );

    final var keyPair =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair();

    final var record =
      new NPAgentLoginChallengeRecord(
        OffsetDateTime.now(),
        "example.com",
        keyPair.publicKey(),
        new NPAgentLoginChallenge(
          command.completion().id(),
          new byte[0]
        )
      );

    Mockito.when(this.challengeGet.execute(any()))
      .thenReturn(Optional.of(record));

    Mockito.when(this.context.agentFindForKey(any()))
      .thenReturn(Optional.empty());

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());

    Mockito.verify(this.challengeGet, new Times(1))
      .execute(command.completion().id());

    Mockito.verifyNoMoreInteractions(this.challengeGet);
    Mockito.verifyNoMoreInteractions(this.challengeDelete);
  }

  /**
   * Fails if the signature cannot be verified.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure2()
    throws Exception
  {
    final var handler = new NPACmdLoginComplete();

    final var keyPair =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair();

    /*
     * The server sent data0, but the client signed data1. The signature
     * will be parsed correctly, but will fail verification.
     */

    final var data0 =
      "ABCDEFGH".getBytes(UTF_8);
    final var data1 =
      "abcdefgh".getBytes(UTF_8);

    final var signature1 =
      keyPair.signData(data1);

    final var command =
      new NPACommandCLoginComplete(
        UUID.randomUUID(),
        new NPAgentLoginChallengeCompletion(
          UUID.randomUUID(),
          signature1
        )
      );

    final var record =
      new NPAgentLoginChallengeRecord(
        OffsetDateTime.now(),
        "example.com",
        keyPair.publicKey(),
        new NPAgentLoginChallenge(
          command.completion().id(),
          data0
        )
      );

    Mockito.when(this.challengeGet.execute(any()))
      .thenReturn(Optional.of(record));

    Mockito.when(this.context.agentFindForKey(keyPair.publicKey()))
      .thenReturn(Optional.of(
        new NPAgentDescription(
          NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
          "Agent",
          keyPair.publicKey(),
          Map.of(),
          Map.of(),
          Map.of()
        )
      ));

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());

    Mockito.verify(this.challengeGet, new Times(1))
      .execute(command.completion().id());

    Mockito.verifyNoMoreInteractions(this.challengeGet);
    Mockito.verifyNoMoreInteractions(this.challengeDelete);
  }

  /**
   * Fails if the signature cannot be verified.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure3()
    throws Exception
  {
    final var handler = new NPACmdLoginComplete();

    final var keyPair =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair();

    final var data0 =
      "ABCDEFGH".getBytes(UTF_8);

    final var command =
      new NPACommandCLoginComplete(
        UUID.randomUUID(),
        new NPAgentLoginChallengeCompletion(
          UUID.randomUUID(),
          new byte[0]
        )
      );

    final var record =
      new NPAgentLoginChallengeRecord(
        OffsetDateTime.now(),
        "example.com",
        keyPair.publicKey(),
        new NPAgentLoginChallenge(
          command.completion().id(),
          data0
        )
      );

    Mockito.when(this.challengeGet.execute(any()))
      .thenReturn(Optional.of(record));

    Mockito.when(this.context.agentFindForKey(keyPair.publicKey()))
      .thenReturn(Optional.of(
        new NPAgentDescription(
          NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
          "Agent",
          keyPair.publicKey(),
          Map.of(),
          Map.of(),
          Map.of()
        )
      ));

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());

    Mockito.verify(this.challengeGet, new Times(1))
      .execute(command.completion().id());

    Mockito.verifyNoMoreInteractions(this.challengeGet);
    Mockito.verifyNoMoreInteractions(this.challengeDelete);
  }

  /**
   * Succeeds if an agent exists with the given key, and the presented signature
   * is valid.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPACmdLoginComplete();

    final var keyPair =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair();

    final var data0 =
      "ABCDEFGH".getBytes(UTF_8);

    final var signature0 =
      keyPair.signData(data0);

    final var command =
      new NPACommandCLoginComplete(
        UUID.randomUUID(),
        new NPAgentLoginChallengeCompletion(
          UUID.randomUUID(),
          signature0
        )
      );

    final var record =
      new NPAgentLoginChallengeRecord(
        OffsetDateTime.now(),
        "example.com",
        keyPair.publicKey(),
        new NPAgentLoginChallenge(
          command.completion().id(),
          data0
        )
      );

    Mockito.when(this.challengeGet.execute(any()))
      .thenReturn(Optional.of(record));

    Mockito.when(this.context.agentFindForKey(keyPair.publicKey()))
      .thenReturn(Optional.of(
        new NPAgentDescription(
          NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
          "Agent",
          keyPair.publicKey(),
          Map.of(),
          Map.of(),
          Map.of()
        )
      ));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    Mockito.verify(this.challengeGet, new Times(1))
      .execute(record.id());

    Mockito.verify(this.challengeDelete, new Times(1))
      .execute(record.id());

    Mockito.verifyNoMoreInteractions(this.challengeGet);
    Mockito.verifyNoMoreInteractions(this.challengeDelete);
  }
}
