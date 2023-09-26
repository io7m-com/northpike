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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemLogAddType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemOutput;
import com.io7m.northpike.server.internal.agents.NPACmdWorkItemOutput;
import com.io7m.northpike.server.internal.agents.NPAgentCommandContextType;
import com.io7m.northpike.strings.NPStringConstantType;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorApiMisuse;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_ACCEPTED;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

/**
 * Tests for a command.
 */

public final class NPACmdWorkItemOutputTest
{
  private NPAgentCommandContextType context;
  private NPDatabaseType database;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.context =
      mock(NPAgentCommandContextType.class);

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

    this.database =
      mock(NPDatabaseType.class);
    this.connection =
      mock(NPDatabaseConnectionType.class);
    this.transaction =
      mock(NPDatabaseTransactionType.class);

    when(this.database.openConnection(any()))
      .thenReturn(this.connection);
    when(this.connection.openTransaction())
      .thenReturn(this.transaction);
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
    final var handler = new NPACmdWorkItemOutput();

    when(this.context.onAuthenticationRequire())
      .thenThrow(new NPPlanException(
        ERROR_AUTHENTICATION.name(),
        errorAuthentication(),
        Map.of(),
        Optional.empty()
      ));

    final var command =
      new NPACommandCWorkItemOutput(
        UUID.randomUUID(),
        new NPWorkItemIdentifier(
          new NPAssignmentExecutionID(UUID.randomUUID()),
          new RDottedName("some.task")
        ),
        "A line."
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_AUTHENTICATION", ex.message());
    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Requires a work item that exists.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure1()
    throws Exception
  {
    final var handler = new NPACmdWorkItemOutput();

    final var agentId =
      NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76");

    when(this.context.onAuthenticationRequire())
      .thenReturn(agentId);
    when(this.context.databaseConnection())
      .thenReturn(this.connection);

    final var get =
      mock(WorkItemGetType.class);

    when(this.transaction.queries(WorkItemGetType.class))
      .thenReturn(get);
    when(get.execute(any()))
      .thenReturn(Optional.empty());

    final var command =
      new NPACommandCWorkItemOutput(
        UUID.randomUUID(),
        new NPWorkItemIdentifier(
          new NPAssignmentExecutionID(UUID.randomUUID()),
          new RDottedName("some.task")
        ),
        "A line."
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_NONEXISTENT", ex.message());
    assertEquals(errorNonexistent(), ex.errorCode());
  }

  /**
   * Requires an accepted work item.
   *
   * @throws Exception On errors
   */

  @Test
  public void testFailure2()
    throws Exception
  {
    final var handler = new NPACmdWorkItemOutput();

    final var agentId =
      NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76");
    final var agentOtherId =
      NPAgentID.of("ff735211-4212-46b5-b03b-d65fb60a0f6d");

    when(this.context.onAuthenticationRequire())
      .thenReturn(agentId);
    when(this.context.databaseConnection())
      .thenReturn(this.connection);

    final var get =
      mock(WorkItemGetType.class);

    when(this.transaction.queries(WorkItemGetType.class))
      .thenReturn(get);
    when(get.execute(any()))
      .thenReturn(Optional.of(
        new NPWorkItem(
          new NPWorkItemIdentifier(
            new NPAssignmentExecutionID(UUID.randomUUID()),
            new RDottedName("some.task")
          ),
          Optional.of(agentOtherId),
          WORK_ITEM_ACCEPTED
        )
      ));

    final var command =
      new NPACommandCWorkItemOutput(
        UUID.randomUUID(),
        new NPWorkItemIdentifier(
          new NPAssignmentExecutionID(UUID.randomUUID()),
          new RDottedName("some.task")
        ),
        "A line."
      );

    final var ex =
      assertThrows(NPException.class, () -> {
        handler.execute(this.context, command);
      });

    assertEquals("ERROR_WORK_ITEM_NOT_YOURS", ex.message());
    assertEquals(errorApiMisuse(), ex.errorCode());
  }

  /**
   * Succeeds if a work item has been accepted before.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSuccess0()
    throws Exception
  {
    final var handler = new NPACmdWorkItemOutput();

    final var agentId =
      NPAgentID.of("ab27f114-6b29-5ab2-a528-b41ef98abe76");

    final var identifier =
      new NPWorkItemIdentifier(
        new NPAssignmentExecutionID(UUID.randomUUID()),
        new RDottedName("some.task")
      );

    final var command =
      new NPACommandCWorkItemOutput(
        UUID.randomUUID(),
        identifier,
        "A line."
      );

    when(this.context.onAuthenticationRequire())
      .thenReturn(agentId);
    when(this.context.databaseConnection())
      .thenReturn(this.connection);

    final var get =
      mock(WorkItemGetType.class);
    final var add =
      mock(WorkItemLogAddType.class);

    when(this.transaction.queries(WorkItemGetType.class))
      .thenReturn(get);
    when(this.transaction.queries(WorkItemLogAddType.class))
      .thenReturn(add);

    when(get.execute(any()))
      .thenReturn(Optional.of(
        new NPWorkItem(
          identifier,
          Optional.of(agentId),
          WORK_ITEM_ACCEPTED
        )
      ));

    final var r = handler.execute(this.context, command);
    assertEquals(r.correlationID(), command.messageID());

    verify(add)
      .execute(
        new WorkItemLogAddType.Parameters(
          identifier,
          "A line."
        )
      );
  }
}
