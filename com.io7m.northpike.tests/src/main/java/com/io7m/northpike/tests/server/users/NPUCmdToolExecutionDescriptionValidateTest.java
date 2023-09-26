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
import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdToolExecutionDescriptionValidate;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.NPTXCompilationResultType;
import com.io7m.northpike.toolexec.NPTXCompilerFactoryType;
import com.io7m.northpike.toolexec.NPTXCompilerType;
import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPUCmdToolExecutionDescriptionValidateTest
{
  private static final NPToolExecutionDescription TOOL_EXECUTION_DESCRIPTION =
    new NPToolExecutionDescription(
      new NPToolExecutionIdentifier(
        NPToolExecutionName.of("x.y"),
        100L
      ),
      NPToolName.of("t"),
      "A description.",
      NPFormatName.of("f"),
      "Some text."
    );

  private NPUserCommandContextType context;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private RPServiceDirectory services;
  private NPTXCompilerFactoryType compilers;
  private NPTXCompilerType compiler;

  @BeforeEach
  public void setup()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());

    this.compilers =
      Mockito.mock(NPTXCompilerFactoryType.class);
    this.compiler =
      Mockito.mock(NPTXCompilerType.class);
    this.context =
      Mockito.mock(NPUserCommandContextType.class);

    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, NPStrings.create(Locale.ROOT));
    this.services.register(NPTXCompilerFactoryType.class, this.compilers);

    Mockito.when(this.context.services())
      .thenReturn(this.services);
    Mockito.when(this.compilers.create(any()))
      .thenReturn(this.compiler);

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
    final var handler = new NPUCmdToolExecutionDescriptionValidate();

    Mockito.when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPUCommandToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        List.of(),
        TOOL_EXECUTION_DESCRIPTION
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Fails if invalid.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPUCmdToolExecutionDescriptionValidate();

    final var command =
      new NPUCommandToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        List.of(),
        TOOL_EXECUTION_DESCRIPTION
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of())
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    final var failure =
      new NPTXCompilationResultType.Failure(
        List.of(
          new NPCompilationMessage(
            NPCompilationMessage.Kind.ERROR,
            1,
            0,
            "Failed!"
          )
        )
      );

    Mockito.when(this.compiler.execute(any(), any(), any()))
      .thenReturn(failure);

    final var r =
      handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());
    assertFalse(r.isValid(false));
  }

  /**
   * Succeeds if validated.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPUCmdToolExecutionDescriptionValidate();

    final var command =
      new NPUCommandToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        List.of(),
        TOOL_EXECUTION_DESCRIPTION
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of())
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    Mockito.when(this.compiler.execute(any(), any(), any()))
      .thenReturn(new NPTXCompilationResultType.Success(
        Mockito.mock(NPTXTypeChecked.class)
      ));

    final var r =
      handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());
    assertTrue(r.isValid(false));
  }
}
