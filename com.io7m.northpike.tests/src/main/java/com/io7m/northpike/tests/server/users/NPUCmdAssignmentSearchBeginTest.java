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
import com.io7m.northpike.database.api.NPAssignmentsPagedType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchBegin;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.server.internal.security.NPSecurityPolicy;
import com.io7m.northpike.server.internal.users.NPUCmdAssignmentSearchBegin;
import com.io7m.northpike.server.internal.users.NPUserCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;
import org.mockito.internal.verification.NoInteractions;
import org.mockito.internal.verification.Times;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorSecurityPolicyDenied;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.when;

/**
 * Tests for a command.
 */

public final class NPUCmdAssignmentSearchBeginTest
{
  private NPUserCommandContextType context;
  private NPDatabaseTransactionType transaction;

  @BeforeEach
  public void setup()
    throws Exception
  {
    NPSecurity.setPolicy(NPSecurityPolicy.open());

    this.context =
      Mockito.mock(NPUserCommandContextType.class);
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
    final var handler = new NPUCmdAssignmentSearchBegin();

    Mockito.when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPUCommandAssignmentSearchBegin(
        UUID.randomUUID(),
        new NPAssignmentSearchParameters(
          new NPComparisonExactType.Anything<>(),
          new NPComparisonExactType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          1000L
        )
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());

    Mockito.verify(this.transaction, new NoInteractions())
      .commit();
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
    final var handler = new NPUCmdAssignmentSearchBegin();

    final var command =
      new NPUCommandAssignmentSearchBegin(
        UUID.randomUUID(),
        new NPAssignmentSearchParameters(
          new NPComparisonExactType.Anything<>(),
          new NPComparisonExactType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          1000L
        )
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

    Mockito.verify(this.transaction, new NoInteractions())
      .commit();
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
    final var handler = new NPUCmdAssignmentSearchBegin();

    final var command =
      new NPUCommandAssignmentSearchBegin(
        UUID.randomUUID(),
        new NPAssignmentSearchParameters(
          new NPComparisonExactType.Anything<>(),
          new NPComparisonExactType.Anything<>(),
          new NPComparisonFuzzyType.Anything<>(),
          1000L
        )
      );

    final var userId =
      new NPUser(
        UUID.fromString("ab27f114-6b29-5ab2-a528-b41ef98abe76"),
        new IdName("x"),
        new MSubject(Set.of(NPSecRole.ASSIGNMENTS_READER.role()))
      );

    Mockito.when(this.context.onAuthenticationRequire())
      .thenReturn(userId);

    final var pageMain =
      new NPPage<>(
        List.of(
          new NPAssignment(
            NPAssignmentName.of("x.y.z0"),
            new NPRepositoryID(randomUUID()),
            NPPlanIdentifier.of("p0", 1L),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          ),
          new NPAssignment(
            NPAssignmentName.of("x.y.z1"),
            new NPRepositoryID(randomUUID()),
            NPPlanIdentifier.of("p0", 1L),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          ),
          new NPAssignment(
            NPAssignmentName.of("x.y.z2"),
            new NPRepositoryID(randomUUID()),
            NPPlanIdentifier.of("p0", 1L),
            NPAssignmentScheduleNone.SCHEDULE_NONE
          )
        ),
        1,
        1,
        0L
      );

    final var pageSummarized =
      new NPPage<>(
        List.of(
          pageMain.items().get(0),
          pageMain.items().get(1),
          pageMain.items().get(2)
        ),
        1,
        1,
        0L
      );

    final var list =
      Mockito.mock(NPDatabaseQueriesAssignmentsType.AssignmentSearchType.class);

    Mockito.when(this.transaction.queries(NPDatabaseQueriesAssignmentsType.AssignmentSearchType.class))
      .thenReturn(list);

    final var paged =
      Mockito.mock(NPAssignmentsPagedType.class);

    Mockito.when(paged.pageCurrent(any()))
      .thenReturn(pageMain);

    Mockito.when(list.execute(any()))
      .thenReturn(paged);

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());
    assertEquals(pageSummarized, r.results());

    Mockito.verify(this.context, new Times(1))
      .setProperty(NPAssignmentsPagedType.class, paged);
    Mockito.verify(this.transaction, new Times(1))
      .queries(NPDatabaseQueriesAssignmentsType.AssignmentSearchType.class);
    Mockito.verify(this.transaction, new Times(1))
      .close();
    Mockito.verifyNoMoreInteractions(this.transaction);
  }
}
