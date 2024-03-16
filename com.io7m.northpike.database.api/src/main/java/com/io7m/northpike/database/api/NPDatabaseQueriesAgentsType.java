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

package com.io7m.northpike.database.api;

import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLabel;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.agents.NPAgentLabelSearchParameters;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeSearchParameters;
import com.io7m.northpike.model.agents.NPAgentSearchParameters;

import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

/**
 * The database queries involving agents.
 */

public sealed interface NPDatabaseQueriesAgentsType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given agent.
   */

  non-sealed interface AgentPutType
    extends NPDatabaseQueryType<NPAgentDescription, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Delete an agent.
   */

  non-sealed interface AgentDeleteType
    extends NPDatabaseQueryType<NPAgentID, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve an agent.
   */

  non-sealed interface AgentGetType
    extends NPDatabaseQueryType<AgentGetType.Parameters, Optional<NPAgentDescription>>,
    NPDatabaseQueriesAgentsType
  {
    /**
     * The parameters.
     *
     * @param agentID        The agent ID
     * @param includeDeleted Whether to include deleted agents
     */

    record Parameters(
      NPAgentID agentID,
      boolean includeDeleted)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(agentID, "agentID");
      }
    }
  }

  /**
   * Retrieve an agent by public key.
   */

  non-sealed interface AgentGetByKeyType
    extends NPDatabaseQueryType<AgentGetByKeyType.Parameters, Optional<NPAgentDescription>>,
    NPDatabaseQueriesAgentsType
  {
    /**
     * The parameters.
     *
     * @param agentKey       The agent key
     * @param includeDeleted Whether to include deleted agents
     */

    record Parameters(
      NPAgentKeyPublicType agentKey,
      boolean includeDeleted)
    {
      /**
       * The parameters.
       */

      public Parameters
      {
        Objects.requireNonNull(agentKey, "agentKey");
      }
    }
  }

  /**
   * List agents.
   */

  non-sealed interface AgentListType
    extends NPDatabaseQueryType<NPAgentSearchParameters, NPAgentPagedType>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Update the given agent label.
   */

  non-sealed interface AgentLabelPutType
    extends NPDatabaseQueryType<NPAgentLabel, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve an agent label.
   */

  non-sealed interface AgentLabelGetType
    extends NPDatabaseQueryType<NPAgentLabelName, Optional<NPAgentLabel>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Search for agent labels.
   */

  non-sealed interface AgentLabelSearchType
    extends NPDatabaseQueryType<NPAgentLabelSearchParameters, NPAgentLabelsPagedType>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Delete an agent label.
   */

  non-sealed interface AgentLabelDeleteType
    extends NPDatabaseQueryType<Set<NPAgentLabelName>, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Create/update a login challenge.
   */

  non-sealed interface AgentLoginChallengePutType
    extends NPDatabaseQueryType<NPAgentLoginChallengeRecord, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve a login challenge.
   */

  non-sealed interface AgentLoginChallengeGetForKeyType
    extends NPDatabaseQueryType<NPAgentKeyPublicType, Optional<NPAgentLoginChallengeRecord>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve a login challenge.
   */

  non-sealed interface AgentLoginChallengeGetType
    extends NPDatabaseQueryType<UUID, Optional<NPAgentLoginChallengeRecord>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Create/update a login challenge.
   */

  non-sealed interface AgentLoginChallengeDeleteType
    extends NPDatabaseQueryType<UUID, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Search for login challenges.
   */

  non-sealed interface AgentLoginChallengeSearchType
    extends NPDatabaseQueryType<NPAgentLoginChallengeSearchParameters, NPAgentLoginChallengePagedType>,
    NPDatabaseQueriesAgentsType
  {

  }
}
