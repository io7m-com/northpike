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

import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemLogRecordOnAgent;
import com.io7m.northpike.model.agents.NPAgentLocalName;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The database queries involving assignment logs.
 */

public sealed interface NPAgentDatabaseQueriesAssignmentLogsType
  extends NPAgentDatabaseQueriesType
{
  /**
   * Add an assignment log.
   */

  non-sealed interface AssignmentLogPutType
    extends NPAgentDatabaseQueryType<NPWorkItemLogRecordOnAgent, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAssignmentLogsType
  {

  }

  /**
   * Get an assignment log.
   */

  non-sealed interface AssignmentLogGetType
    extends NPAgentDatabaseQueryType<
    AssignmentLogGetType.Parameters, Optional<NPWorkItemLogRecordOnAgent>>,
    NPAgentDatabaseQueriesAssignmentLogsType
  {
    /**
     * The parameters.
     *
     * @param identifier The identifier
     * @param index      The log index
     */

    record Parameters(
      NPWorkItemIdentifier identifier,
      long index)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(identifier, "identifier");
      }
    }
  }

  /**
   * Delete an assignment log.
   */

  non-sealed interface AssignmentLogDeleteType
    extends NPAgentDatabaseQueryType<
    AssignmentLogDeleteType.Parameters, NPAgentDatabaseUnit>,
    NPAgentDatabaseQueriesAssignmentLogsType
  {
    /**
     * The parameters.
     *
     * @param agent      The agent
     * @param identifier The identifier
     * @param index      The log index
     */

    record Parameters(
      NPAgentLocalName agent,
      NPWorkItemIdentifier identifier,
      long index)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(agent, "agent");
        Objects.requireNonNull(identifier, "identifier");
      }
    }
  }

  /**
   * List assignment logs.
   */

  non-sealed interface AssignmentLogListType
    extends NPAgentDatabaseQueryType<
    AssignmentLogListType.Parameters, List<NPWorkItemLogRecordOnAgent>>,
    NPAgentDatabaseQueriesAssignmentLogsType
  {
    /**
     * The parameters.
     *
     * @param agent  The agent
     * @param offset The starting offset
     * @param limit  The limit
     */

    record Parameters(
      NPAgentLocalName agent,
      long offset,
      long limit)
    {

    }
  }
}
