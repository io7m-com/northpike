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


package com.io7m.northpike.agent.internal.console;


import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerPutType;
import com.io7m.northpike.agent.internal.events.NPAgentServerUpdated;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;

/**
 * @see NPACCommandServerPut
 */

public final class NPACCmdServerPut
  extends NPACCmdAbstract<NPACResponseOK, NPACCommandServerPut>
{
  /**
   * @see NPACCommandServerPut
   */

  public NPACCmdServerPut()
  {
    super(NPACCommandServerPut.class);
  }

  @Override
  public NPACResponseOK execute(
    final NPACCommandContextType context,
    final NPACCommandServerPut command)
    throws NPException
  {
    context.onAuthenticationRequire();

    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        transaction.queries(ServerPutType.class).execute(command.server());
        transaction.commit();
        context.publishEvent(new NPAgentServerUpdated(command.server().id()));
        return NPACResponseOK.createCorrelated(command);
      }
    }
  }
}
