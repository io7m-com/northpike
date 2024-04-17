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

import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionWorkItemsType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionWorkItems;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionWorkItems;
import com.io7m.northpike.server.internal.security.NPSecurity;

import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;

/**
 * @see NPUCommandAssignmentExecutionWorkItems
 */

public final class NPUCmdAssignmentExecutionWorkItems
  extends NPUCmdAbstract<
  NPUResponseAssignmentExecutionWorkItems, NPUCommandAssignmentExecutionWorkItems>
{
  /**
   * @see NPUCommandAssignmentExecutionWorkItems
   */

  public NPUCmdAssignmentExecutionWorkItems()
  {
    super(NPUCommandAssignmentExecutionWorkItems.class);
  }

  @Override
  public NPUResponseAssignmentExecutionWorkItems execute(
    final NPUserCommandContextType context,
    final NPUCommandAssignmentExecutionWorkItems command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.ASSIGNMENT_EXECUTIONS.object(),
      NPSecAction.READ.action()
    );

    try (var transaction = context.transaction(NORTHPIKE_READ_ONLY)) {
      return new NPUResponseAssignmentExecutionWorkItems(
        UUID.randomUUID(),
        command.messageID(),
        transaction.queries(AssignmentExecutionWorkItemsType.class)
          .execute(command.execution())
      );
    }
  }
}
