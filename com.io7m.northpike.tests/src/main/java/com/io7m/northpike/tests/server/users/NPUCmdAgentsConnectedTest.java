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
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.user.NPUCommandAgentsConnected;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdAgentsConnected;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorSecurityPolicyDenied;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPUCmdAgentsConnectedTest
{
  private NPUserCommandContextType context;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;

  @BeforeEach
  public void setup()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());

    this.context =
      Mockito.mock(NPUserCommandContextType.class);

    this.connection =
      Mockito.mock(NPDatabaseConnectionType.class);
    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);

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
    final var handler = new NPUCmdAgentsConnected();

    Mockito.when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPUCommandAgentsConnected(
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
   * Requires permissions.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPUCmdAgentsConnected();

    final var command =
      new NPUCommandAgentsConnected(
        UUID.randomUUID()
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of())
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("Operation not permitted.", ex.message());
    assertEquals(errorSecurityPolicyDenied(), ex.errorCode());
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
    final var handler = new NPUCmdAgentsConnected();

    final var command =
      new NPUCommandAgentsConnected(
        UUID.randomUUID()
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(NPSecRole.AGENTS_READER.role()))
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    final var agents =
      Mockito.mock(NPAgentServiceType.class);

    final var services = new RPServiceDirectory();
    services.register(NPAgentServiceType.class, agents);

    Mockito.when(this.context.services())
      .thenReturn(services);

    final var agentSet =
      Set.of(
        new NPAgentID(UUID.randomUUID()),
        new NPAgentID(UUID.randomUUID()),
        new NPAgentID(UUID.randomUUID()),
        new NPAgentID(UUID.randomUUID()),
        new NPAgentID(UUID.randomUUID())
      );

    Mockito.when(agents.findAgentsConnected())
      .thenReturn(agentSet);

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    assertEquals(agentSet, r.agents());
  }
}
