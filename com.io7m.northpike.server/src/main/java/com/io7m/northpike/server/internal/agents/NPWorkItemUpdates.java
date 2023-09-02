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


package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemLogAddType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemPutType;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.strings.NPStringConstantType;

import java.util.Optional;
import java.util.function.BiFunction;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorApiMisuse;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_WORK_ITEM_NOT_YOURS;

/**
 * Functions to update work items.
 */

public final class NPWorkItemUpdates
{
  private NPWorkItemUpdates()
  {

  }

  /**
   * Set the status of a work item.
   *
   * @param connection The database connection.
   * @param onFail     A function called on failure
   * @param agentId    The agent ID
   * @param identifier The identifier
   * @param newStatus  The new status
   *
   * @throws NPException On errors
   */

  public static void setWorkItemStatus(
    final NPDatabaseConnectionType connection,
    final BiFunction<NPStringConstantType, NPErrorCode, NPException> onFail,
    final NPAgentID agentId,
    final NPWorkItemIdentifier identifier,
    final NPWorkItemStatus newStatus)
    throws NPException
  {
    try (var transaction = connection.openTransaction()) {
      final var get =
        transaction.queries(WorkItemGetType.class);
      final var put =
        transaction.queries(WorkItemPutType.class);

      /*
       * The work item doesn't necessarily exist.
       */

      final var existing =
        get.execute(identifier)
          .orElseThrow(() -> {
            return onFail.apply(ERROR_NONEXISTENT, errorNonexistent());
          });

      /*
       * The existing work item might have a different agent selected.
       */

      if (existing.selectedAgent().isPresent()) {
        if (!existing.hasAgent(agentId)) {
          throw onFail.apply(ERROR_WORK_ITEM_NOT_YOURS, errorApiMisuse());
        }
      }

      put.execute(
        new NPWorkItem(existing.identifier(), Optional.of(agentId), newStatus)
      );
      transaction.commit();
    }
  }

  /**
   * Add a line of logging output to the work item.
   *
   * @param connection The database connection.
   * @param onFail     A function called on failure
   * @param agentId    The agent ID
   * @param identifier The identifier
   * @param line       The output line
   *
   * @throws NPException On errors
   */

  public static void addWorkItemLogLine(
    final NPDatabaseConnectionType connection,
    final BiFunction<NPStringConstantType, NPErrorCode, NPException> onFail,
    final NPAgentID agentId,
    final NPWorkItemIdentifier identifier,
    final String line)
    throws NPException
  {
    try (var transaction = connection.openTransaction()) {
      final var get =
        transaction.queries(WorkItemGetType.class);
      final var add =
        transaction.queries(WorkItemLogAddType.class);

      /*
       * The work item doesn't necessarily exist.
       */

      final var existing =
        get.execute(identifier)
          .orElseThrow(() -> {
            return onFail.apply(ERROR_NONEXISTENT, errorNonexistent());
          });

      /*
       * The existing work item might have a different agent selected.
       */

      if (existing.selectedAgent().isPresent()) {
        if (!existing.hasAgent(agentId)) {
          throw onFail.apply(ERROR_WORK_ITEM_NOT_YOURS, errorApiMisuse());
        }
      }

      add.execute(new WorkItemLogAddType.Parameters(identifier, line));
      transaction.commit();
    }
  }
}
