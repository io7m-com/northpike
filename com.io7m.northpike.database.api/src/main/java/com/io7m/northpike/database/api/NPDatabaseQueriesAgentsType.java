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

  non-sealed interface PutType
    extends NPDatabaseQueryType<NPAgentDescription, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Delete an agent.
   */

  non-sealed interface DeleteType
    extends NPDatabaseQueryType<NPAgentID, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve an agent.
   */

  non-sealed interface GetType
    extends NPDatabaseQueryType<NPAgentID, Optional<NPAgentDescription>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve an agent by public key.
   */

  non-sealed interface GetByKeyType
    extends NPDatabaseQueryType<NPAgentKeyPublicType, Optional<NPAgentDescription>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * List agents.
   */

  non-sealed interface ListType
    extends NPDatabaseQueryType<NPAgentSearchParameters, NPAgentPagedType>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Update the given agent label.
   */

  non-sealed interface LabelPutType
    extends NPDatabaseQueryType<NPAgentLabel, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve an agent label.
   */

  non-sealed interface LabelGetType
    extends NPDatabaseQueryType<NPAgentLabelName, Optional<NPAgentLabel>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Search for agent labels.
   */

  non-sealed interface LabelSearchType
    extends NPDatabaseQueryType<NPAgentLabelSearchParameters, NPAgentLabelsPagedType>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Delete an agent label.
   */

  non-sealed interface LabelDeleteType
    extends NPDatabaseQueryType<Set<NPAgentLabelName>, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Create/update a login challenge.
   */

  non-sealed interface LoginChallengePutType
    extends NPDatabaseQueryType<NPAgentLoginChallengeRecord, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve a login challenge.
   */

  non-sealed interface LoginChallengeGetForKeyType
    extends NPDatabaseQueryType<NPAgentKeyPublicType, Optional<NPAgentLoginChallengeRecord>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Retrieve a login challenge.
   */

  non-sealed interface LoginChallengeGetType
    extends NPDatabaseQueryType<UUID, Optional<NPAgentLoginChallengeRecord>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Create/update a login challenge.
   */

  non-sealed interface LoginChallengeDeleteType
    extends NPDatabaseQueryType<UUID, NPDatabaseUnit>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * Search for login challenges.
   */

  non-sealed interface LoginChallengeSearchType
    extends NPDatabaseQueryType<NPAgentLoginChallengeSearchParameters, NPAgentLoginChallengePagedType>,
    NPDatabaseQueriesAgentsType
  {

  }
}
