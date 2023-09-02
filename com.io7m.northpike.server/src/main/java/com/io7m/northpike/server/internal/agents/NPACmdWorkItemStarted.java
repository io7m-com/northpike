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

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemStarted;
import com.io7m.northpike.protocol.agent.NPAResponseOK;

import static com.io7m.northpike.model.NPWorkItemStatus.WORK_ITEM_RUNNING;

/**
 * @see NPACommandCWorkItemStarted
 */

public final class NPACmdWorkItemStarted
  implements NPAgentCommandExecutorType<NPAResponseOK, NPACommandCWorkItemStarted>
{
  /**
   * @see NPACommandCWorkItemStarted
   */

  public NPACmdWorkItemStarted()
  {

  }

  @Override
  public NPAResponseOK execute(
    final NPAgentCommandContextType context,
    final NPACommandCWorkItemStarted command)
    throws NPException
  {
    final var agentId = context.onAuthenticationRequire();

    try (var connection = context.databaseConnection()) {
      NPWorkItemUpdates.setWorkItemStatus(
        connection,
        context::fail,
        agentId,
        command.identifier(),
        WORK_ITEM_RUNNING
      );
    }

    context.onWorkItemStatusChanged(command.identifier(), WORK_ITEM_RUNNING);
    return NPAResponseOK.createCorrelated(command);
  }
}
