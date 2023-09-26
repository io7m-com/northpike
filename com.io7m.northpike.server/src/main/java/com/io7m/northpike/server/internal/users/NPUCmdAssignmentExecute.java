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


package com.io7m.northpike.server.internal.users;

import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAuditType;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecute;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.assignments.NPAssignmentServiceType;
import com.io7m.northpike.server.internal.security.NPSecurity;

import static java.util.Map.entry;
import static java.util.Map.ofEntries;

/**
 * @see NPUCommandAssignmentExecute
 */

public final class NPUCmdAssignmentExecute
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandAssignmentExecute>
{
  /**
   * @see NPUCommandAssignmentExecute
   */

  public NPUCmdAssignmentExecute()
  {
    super(NPUCommandAssignmentExecute.class);
  }

  private static void logAuditEvent(
    final NPUserCommandContextType context,
    final NPUCommandAssignmentExecute command,
    final NPUser user,
    final NPClockServiceType clock)
    throws NPException
  {
    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var owner = new NPAuditUserOrAgentType.User(user.userId());
        transaction.setOwner(owner);
        transaction.queries(NPDatabaseQueriesAuditType.EventAddType.class)
          .execute(new NPAuditEvent(
            clock.now(),
            owner,
            "ASSIGNMENT_EXECUTE_REQUESTED",
            ofEntries(
              entry("ASSIGNMENT", command.assignment().toString()),
              entry("COMMIT", command.commit().value())
            )
          ));
        transaction.commit();
      }
    }
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandAssignmentExecute command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.ASSIGNMENTS.object(),
      NPSecAction.EXECUTE.action()
    );

    final var services =
      context.services();
    final var assignmentService =
      services.requireService(NPAssignmentServiceType.class);
    final var clock =
      services.requireService(NPClockServiceType.class);

    assignmentService.requestExecution(
      new NPAssignmentExecutionRequest(command.assignment(), command.commit()));

    logAuditEvent(context, command, user, clock);
    return NPUResponseOK.createCorrelated(command);
  }
}
