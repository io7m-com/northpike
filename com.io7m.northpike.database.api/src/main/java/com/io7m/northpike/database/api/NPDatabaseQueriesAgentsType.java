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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabel;
import com.io7m.northpike.model.NPAgentListParameters;

import java.util.Optional;

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
   * Retrieve an agent.
   */

  non-sealed interface GetType
    extends NPDatabaseQueryType<NPAgentID, Optional<NPAgentDescription>>,
    NPDatabaseQueriesAgentsType
  {

  }

  /**
   * List agents.
   */

  non-sealed interface ListType
    extends NPDatabaseQueryType<NPAgentListParameters, NPAgentPagedType>,
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
    extends NPDatabaseQueryType<RDottedName, Optional<NPAgentLabel>>,
    NPDatabaseQueriesAgentsType
  {

  }
}
