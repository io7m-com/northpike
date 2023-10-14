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


package com.io7m.northpike.agent.database.api;

import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;

import java.util.Optional;

/**
 * The database queries involving servers.
 */

public sealed interface NPAgentDatabaseQueriesServersType
  extends NPAgentDatabaseQueriesType
{
  /**
   * Update the given server.
   */

  non-sealed interface ServerPutType
    extends NPAgentDatabaseQueryType<NPAgentServerDescription, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesServersType
  {

  }

  /**
   * Delete a server.
   */

  non-sealed interface ServerDeleteType
    extends NPAgentDatabaseQueryType<NPAgentServerID, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesServersType
  {

  }

  /**
   * Retrieve a server.
   */

  non-sealed interface ServerGetType
    extends NPAgentDatabaseQueryType<NPAgentServerID, Optional<NPAgentServerDescription>>,
    NPAgentDatabaseQueriesServersType
  {

  }
}
