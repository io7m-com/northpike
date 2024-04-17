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


package com.io7m.northpike.tests.server.users;

import com.io7m.idstore.model.IdName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeDeleteType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicEd448Type;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeAgentCreate;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdAgentLoginChallengeAgentCreate;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.Times;

import java.time.OffsetDateTime;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorDuplicate;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorSecurityPolicyDenied;
import static com.io7m.northpike.model.security.NPSecRole.AGENTS_WRITER;
import static com.io7m.northpike.model.security.NPSecRole.AGENT_LOGIN_CHALLENGE_READER;
import static com.io7m.northpike.model.security.NPSecRole.AGENT_LOGIN_CHALLENGE_WRITER;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.when;

/**
 * Tests for a command.
 */

public final class NPUCmdAgentLoginChallengeAgentCreateTest
{
  private NPUserCommandContextType context;
  private NPDatabaseTransactionType transaction;
  private NPAgentKeyPublicEd448Type key;
  private NPStrings strings;
  private RPServiceDirectory services;

  @BeforeEach
  public void setup()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());

    this.strings =
      NPStrings.create(Locale.ROOT);

    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, this.strings);

    this.key =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair()
        .publicKey();

    this.context =
      Mockito.mock(NPUserCommandContextType.class);

    when(this.context.services())
      .thenReturn(this.services);

    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);

    when(this.context.transaction())
      .thenReturn(this.transaction);
    when(this.context.transaction(any()))
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
    final var handler = new NPUCmdAgentLoginChallengeAgentCreate();

    when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPUCommandAgentLoginChallengeAgentCreate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPAgentID(UUID.randomUUID()),
        "agent"
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Requires permissions.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPUCmdAgentLoginChallengeAgentCreate();

    final var command =
      new NPUCommandAgentLoginChallengeAgentCreate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPAgentID(UUID.randomUUID()),
        "agent"
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of())
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("Operation not permitted.", ex.message());
    assertEquals(errorSecurityPolicyDenied(), ex.errorCode());
  }

  /**
   * Fails if the agent already exists.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure2()
    throws Exception
  {
    final var handler = new NPUCmdAgentLoginChallengeAgentCreate();

    final var command =
      new NPUCommandAgentLoginChallengeAgentCreate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPAgentID(UUID.randomUUID()),
        "agent"
      );

    final var user =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(
          AGENT_LOGIN_CHALLENGE_WRITER.role(),
          AGENT_LOGIN_CHALLENGE_READER.role(),
          AGENTS_WRITER.role()
        ))
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(user);

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);

    final var parameters =
      new AgentGetType.Parameters(command.agent(), true);

    when(agentGet.execute(eq(parameters)))
      .thenReturn(Optional.of(
        new NPAgentDescription(
          command.agent(),
          "agent",
          this.key,
          Map.of(),
          Map.of(),
          Map.of()
        )
      ));

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("Object already exists.", ex.message());
    assertEquals(errorDuplicate(), ex.errorCode());
  }

  /**
   * Fails if the challenge doesn't exist.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure3()
    throws Exception
  {
    final var handler = new NPUCmdAgentLoginChallengeAgentCreate();

    final var command =
      new NPUCommandAgentLoginChallengeAgentCreate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPAgentID(UUID.randomUUID()),
        "agent"
      );

    final var user =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(
          AGENT_LOGIN_CHALLENGE_WRITER.role(),
          AGENT_LOGIN_CHALLENGE_READER.role(),
          AGENTS_WRITER.role()
        ))
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(user);

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    final var loginChallengeGet =
      Mockito.mock(AgentLoginChallengeGetType.class);
    final var agentPut =
      Mockito.mock(AgentPutType.class);
    final var loginChallengeDelete =
      Mockito.mock(AgentLoginChallengeDeleteType.class);

    when(this.transaction.queries(AgentPutType.class))
      .thenReturn(agentPut);
    when(this.transaction.queries(AgentLoginChallengeDeleteType.class))
      .thenReturn(loginChallengeDelete);
    when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);
    when(this.transaction.queries(AgentLoginChallengeGetType.class))
      .thenReturn(loginChallengeGet);

    final var parameters =
      new AgentGetType.Parameters(command.agent(), true);

    when(agentGet.execute(eq(parameters)))
      .thenReturn(Optional.empty());

    when(loginChallengeGet.execute(eq(command.loginChallenge())))
      .thenReturn(Optional.empty());

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("Object does not exist.", ex.message());
    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Fails if the challenge doesn't exist.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPUCmdAgentLoginChallengeAgentCreate();

    final var command =
      new NPUCommandAgentLoginChallengeAgentCreate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPAgentID(UUID.randomUUID()),
        "agent"
      );

    final var user =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(
          AGENT_LOGIN_CHALLENGE_WRITER.role(),
          AGENT_LOGIN_CHALLENGE_READER.role(),
          AGENTS_WRITER.role()
        ))
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(user);

    final var agentGet =
      Mockito.mock(AgentGetType.class);
    final var loginChallengeGet =
      Mockito.mock(AgentLoginChallengeGetType.class);
    final var agentPut =
      Mockito.mock(AgentPutType.class);
    final var loginChallengeDelete =
      Mockito.mock(AgentLoginChallengeDeleteType.class);

    when(this.transaction.queries(AgentPutType.class))
      .thenReturn(agentPut);
    when(this.transaction.queries(AgentLoginChallengeDeleteType.class))
      .thenReturn(loginChallengeDelete);
    when(this.transaction.queries(AgentGetType.class))
      .thenReturn(agentGet);
    when(this.transaction.queries(AgentLoginChallengeGetType.class))
      .thenReturn(loginChallengeGet);

    final var parameters =
      new AgentGetType.Parameters(command.agent(), true);

    when(agentGet.execute(eq(parameters)))
      .thenReturn(Optional.empty());

    when(loginChallengeGet.execute(eq(command.loginChallenge())))
      .thenReturn(Optional.of(
        new NPAgentLoginChallengeRecord(
          OffsetDateTime.now(),
          "localhost",
          this.key,
          new NPAgentLoginChallenge(
            command.loginChallenge(),
            "challenge".getBytes(UTF_8)
          )
        )
      ));

    final var r = handler.execute(this.context, command);

    Mockito.verify(agentPut, new Times(1))
      .execute(any());
    Mockito.verify(loginChallengeDelete, new Times(1))
      .execute(eq(command.loginChallenge()));
  }
}
