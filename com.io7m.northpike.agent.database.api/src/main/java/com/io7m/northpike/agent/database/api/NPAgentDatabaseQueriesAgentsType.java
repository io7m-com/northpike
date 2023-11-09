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

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPPageSizes;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The database queries involving agents.
 */

public sealed interface NPAgentDatabaseQueriesAgentsType
  extends NPAgentDatabaseQueriesType
{
  /**
   * Update the given agent.
   */

  non-sealed interface AgentPutType
    extends NPAgentDatabaseQueryType<NPAgentLocalDescription, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAgentsType
  {

  }

  /**
   * Delete an agent.
   */

  non-sealed interface AgentDeleteType
    extends NPAgentDatabaseQueryType<NPAgentLocalName, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve an agent.
   */

  non-sealed interface AgentGetType
    extends NPAgentDatabaseQueryType<NPAgentLocalName, Optional<NPAgentLocalDescription>>,
    NPAgentDatabaseQueriesAgentsType
  {

  }

  /**
   * Set the work executor for the given agent.
   */

  non-sealed interface AgentWorkExecPutType
    extends NPAgentDatabaseQueryType<AgentWorkExecPutType.Parameters, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAgentsType
  {
    /**
     * The parameters.
     *
     * @param agent        The agent name
     * @param workExecutor The work executor
     */

    record Parameters(
      NPAgentLocalName agent,
      Optional<NPAWorkExecutorConfiguration> workExecutor)
    {
      /**
       * The search parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(agent, "agent");
        Objects.requireNonNull(workExecutor, "workExecutor");
      }
    }
  }

  /**
   * Retrieve the work executor for the given agent, if any.
   */

  non-sealed interface AgentWorkExecGetType
    extends NPAgentDatabaseQueryType<NPAgentLocalName, Optional<NPAWorkExecutorConfiguration>>,
    NPAgentDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve the server associated with the given agent, if any.
   */

  non-sealed interface AgentServerGetType
    extends NPAgentDatabaseQueryType<NPAgentLocalName, Optional<NPAgentServerID>>,
    NPAgentDatabaseQueriesAgentsType
  {

  }

  /**
   * Set the server associated with the given agent.
   */

  non-sealed interface AgentServerAssignType
    extends NPAgentDatabaseQueryType<AgentServerAssignType.Parameters, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAgentsType
  {
    /**
     * The parameters.
     *
     * @param agent  The agent name
     * @param server The server
     */

    record Parameters(
      NPAgentLocalName agent,
      NPAgentServerID server)
    {
      /**
       * The search parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(agent, "agent");
        Objects.requireNonNull(server, "server");
      }
    }
  }

  /**
   * Unset the server associated with the given agent.
   */

  non-sealed interface AgentServerUnassignType
    extends NPAgentDatabaseQueryType<NPAgentLocalName, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAgentsType
  {

  }

  /**
   * List agents.
   */

  non-sealed interface AgentListType
    extends NPAgentDatabaseQueryType<AgentListType.Parameters, List<NPAgentLocalName>>,
    NPAgentDatabaseQueriesAgentsType
  {
    /**
     * The parameters.
     *
     * @param offset The starting agent name
     * @param limit  The limit on the number of results
     */

    record Parameters(
      Optional<NPAgentLocalName> offset,
      long limit)
    {
      /**
       * The search parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(offset, "offset");
        limit = NPPageSizes.clampPageSize(limit);
      }
    }
  }
}
