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
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.compiler.NPPlanCompilationResultType;
import com.io7m.northpike.plans.compiler.NPPlanCompilerFactoryType;
import com.io7m.northpike.plans.compiler.NPPlanCompilerType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerType;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdPlanPut;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
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
import static com.io7m.northpike.model.NPStandardErrorCodes.errorCompilationFailed;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorSecurityPolicyDenied;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static com.io7m.northpike.tests.server.users.NPUCmdPlanGetTest.PLAN_DESCRIPTION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;

/**
 * Tests for a command.
 */

public final class NPUCmdPlanPutTest
{
  private NPUserCommandContextType context;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private RPServiceDirectory services;
  private NPPlanCompilerFactoryType compilers;
  private NPPlanCompilerType  compiler;
  private NPPlanSerializerFactoryType serializers;
  private NPPlanSerializerType serializer;

  @BeforeEach
  public void setup()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());

    this.serializers =
      Mockito.mock(NPPlanSerializerFactoryType.class);
    this.serializer =
      Mockito.mock(NPPlanSerializerType.class);
    this.compilers =
      Mockito.mock(NPPlanCompilerFactoryType.class);
    this.compiler =
      Mockito.mock(NPPlanCompilerType .class);
    this.context =
      Mockito.mock(NPUserCommandContextType.class);

    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, NPStrings.create(Locale.ROOT));
    this.services.register(NPPlanCompilerFactoryType.class, this.compilers);
    this.services.register(NPPlanSerializerFactoryType.class, this.serializers);

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

    Mockito.doAnswer(invocationOnMock -> {
      final var message =
        invocationOnMock.getArgument(0, NPStringConstantType.class);
      final var errorCode =
        invocationOnMock.getArgument(1, NPErrorCode.class);
      final var remediation =
        invocationOnMock.getArgument(2, NPStringConstantType.class);

      return new NPException(
        message.toString(),
        errorCode,
        Map.of(),
        Optional.of(remediation.toString())
      );
    }).when(this.context).failWithRemediation(any(), any(), any());
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
    final var handler = new NPUCmdPlanPut();

    Mockito.when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPUCommandPlanPut(
        UUID.randomUUID(),
        PLAN_DESCRIPTION
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Fails if not permitted.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPUCmdPlanPut();

    final var command =
      new NPUCommandPlanPut(
        UUID.randomUUID(),
        PLAN_DESCRIPTION
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
   * Fails if not valid.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure2()
    throws Exception
  {
    final var handler = new NPUCmdPlanPut();

    final var command =
      new NPUCommandPlanPut(
        UUID.randomUUID(),
        PLAN_DESCRIPTION
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(NPSecRole.PLANS_WRITER.role()))
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    final var failure =
      new NPPlanCompilationResultType.Failure(
        List.of(
          new NPCompilationMessage(
            NPCompilationMessage.Kind.ERROR,
            1,
            0,
            "Failed!"
          )
        )
      );

    Mockito.when(this.compiler.execute(any(), any()))
      .thenReturn(failure);

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_COMPILATION_FAILED", ex.message());
    assertEquals(errorCompilationFailed(), ex.errorCode());
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
    final var handler = new NPUCmdPlanPut();

    final var command =
      new NPUCommandPlanPut(
        UUID.randomUUID(),
        PLAN_DESCRIPTION
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(NPSecRole.PLANS_WRITER.role()))
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    Mockito.when(this.compiler.execute(any(), any()))
      .thenReturn(new NPPlanCompilationResultType.Success(
        Mockito.mock(NPPlanType.class)
      ));

    final var put =
      Mockito.mock(NPDatabaseQueriesPlansType.PutType.class);

    Mockito.when(this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class))
      .thenReturn(put);

    final var r =
      handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());
  }
}
