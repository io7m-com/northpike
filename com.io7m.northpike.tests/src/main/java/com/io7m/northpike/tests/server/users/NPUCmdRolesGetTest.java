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
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesGet;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdRolesGet;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.when;

/**
 * Tests for a command.
 */

public final class NPUCmdRolesGetTest
{
  private NPUserCommandContextType context;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseQueriesUsersType.GetType userGet;
  private NPDatabaseQueriesUsersType.PutType userPut;

  @BeforeEach
  public void setup()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());

    this.context =
      Mockito.mock(NPUserCommandContextType.class);

    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);
    this.userGet =
      Mockito.mock(NPDatabaseQueriesUsersType.GetType.class);
    this.userPut =
      Mockito.mock(NPDatabaseQueriesUsersType.PutType.class);

    when(this.context.transaction())
      .thenReturn(this.transaction);
    when(this.context.transaction(any()))
      .thenReturn(this.transaction);

    when(this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class))
        .thenReturn(this.userGet);
    when(this.transaction.queries(NPDatabaseQueriesUsersType.PutType.class))
      .thenReturn(this.userPut);

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
    final var handler = new NPUCmdRolesGet();

    when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPUCommandUserRolesGet(
        UUID.randomUUID(),
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
   * Requires that a user exists.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure2()
    throws Exception
  {
    final var handler = new NPUCmdRolesGet();

    final var user0 =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(
          MRoleName.of("role0")
        ))
      );

    final var user1 =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe77"),
        new IdName("y"),
        new MSubject(Set.of())
      );

    final var command =
      new NPUCommandUserRolesGet(
        UUID.randomUUID(),
        user1.userId()
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(user0);

    when(this.userGet.execute(user1.userId()))
      .thenReturn(Optional.empty());

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_NONEXISTENT", ex.message());
    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Requires roles.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPUCmdRolesGet();

    final var user0 =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(
          MRoleName.of("role0")
        ))
      );

    final var user1 =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe77"),
        new IdName("y"),
        new MSubject(Set.of())
      );

    final var command =
      new NPUCommandUserRolesGet(
        UUID.randomUUID(),
        user1.userId()
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(user0);

    when(this.userGet.execute(user1.userId()))
      .thenReturn(Optional.of(user1));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    assertEquals(user1.subject().roles(), r.roles());
  }
}
