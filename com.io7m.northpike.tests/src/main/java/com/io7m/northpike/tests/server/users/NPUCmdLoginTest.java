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

import com.io7m.idstore.model.IdEmail;
import com.io7m.idstore.model.IdName;
import com.io7m.idstore.model.IdNonEmptyList;
import com.io7m.idstore.model.IdPasswordAlgorithmRedacted;
import com.io7m.idstore.model.IdRealName;
import com.io7m.idstore.model.IdUser;
import com.io7m.idstore.protocol.user.IdUResponseLogin;
import com.io7m.idstore.user_client.api.IdUClientType;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdLogin;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.net.URI;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPUCmdLoginTest
{
  private NPUserCommandContextType context;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private IdUClientType idstore;
  private NPDatabaseQueriesUsersType.GetType userGet;

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
    this.userGet =
      Mockito.mock(NPDatabaseQueriesUsersType.GetType.class);

    Mockito.when(this.context.databaseConnection())
      .thenReturn(this.connection);
    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);
    Mockito.when(this.transaction.queries(NPDatabaseQueriesUsersType.GetType.class))
      .thenReturn(this.userGet);

    this.idstore =
      Mockito.mock(IdUClientType.class);

    Mockito.when(this.context.createIdstoreClient())
      .thenReturn(this.idstore);
    Mockito.when(this.context.idstoreLoginURI())
      .thenReturn(URI.create("http://www.example.com"));

    Mockito.doAnswer(invocationOnMock -> {
      final var cause =
        invocationOnMock.getArgument(0, Exception.class);
      final var message =
        invocationOnMock.getArgument(1, NPStringConstantType.class);
      final var errorCode =
        invocationOnMock.getArgument(2, NPErrorCode.class);

      return new NPException(
        message.toString(),
        cause,
        errorCode,
        Map.of(),
        Optional.empty()
      );
    }).when(this.context).fail(any(), any(), any());
  }

  /**
   * Fails if no user exists with the given credentials.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure0()
    throws Exception
  {
    final var handler = new NPUCmdLogin();

    final var command =
      new NPUCommandLogin(
        UUID.randomUUID(),
        new IdName("x"),
        "y"
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Fails if no user exists with the given credentials.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPUCmdLogin();

    final var command =
      new NPUCommandLogin(
        UUID.randomUUID(),
        new IdName("x"),
        "y"
      );

    final var user =
      new IdUser(
        UUID.randomUUID(),
        command.name(),
        new IdRealName("Example"),
        new IdNonEmptyList<>(new IdEmail("x@example.com"), List.of()),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        IdPasswordAlgorithmRedacted.create()
          .createHashed("x")
      );

    Mockito.when(this.idstore.connectOrThrow(any()))
      .thenReturn(new IdUResponseLogin(
        UUID.randomUUID(),
        user
      ));

    Mockito.when(this.userGet.execute(user.id()))
      .thenReturn(Optional.empty());

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Fails if the user doesn't have the required role.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure2()
    throws Exception
  {
    final var handler = new NPUCmdLogin();

    final var command =
      new NPUCommandLogin(
        UUID.randomUUID(),
        new IdName("x"),
        "y"
      );

    final var user =
      new IdUser(
        UUID.randomUUID(),
        command.name(),
        new IdRealName("Example"),
        new IdNonEmptyList<>(new IdEmail("x@example.com"), List.of()),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        IdPasswordAlgorithmRedacted.create()
          .createHashed("x")
      );

    Mockito.when(this.idstore.connectOrThrow(any()))
      .thenReturn(new IdUResponseLogin(
        UUID.randomUUID(),
        user
      ));

    Mockito.when(this.userGet.execute(user.id()))
      .thenReturn(Optional.of(
        new NPUser(
          user.id(),
          user.idName(),
          new MSubject(Set.of())
        )
      ));

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Succeeds if a user exists with the given name/password.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPUCmdLogin();

    final var command =
      new NPUCommandLogin(
        UUID.randomUUID(),
        new IdName("x"),
        "y"
      );

    final var user =
      new IdUser(
        UUID.randomUUID(),
        command.name(),
        new IdRealName("Example"),
        new IdNonEmptyList<>(new IdEmail("x@example.com"), List.of()),
        OffsetDateTime.now(),
        OffsetDateTime.now(),
        IdPasswordAlgorithmRedacted.create()
          .createHashed("x")
      );

    Mockito.when(this.idstore.connectOrThrow(any()))
      .thenReturn(new IdUResponseLogin(
        UUID.randomUUID(),
        user
      ));

    Mockito.when(this.userGet.execute(user.id()))
      .thenReturn(Optional.of(
        new NPUser(
          user.id(),
          user.idName(),
          new MSubject(Set.of(NPSecRole.LOGIN.role()))
        )
      ));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());
  }
}
