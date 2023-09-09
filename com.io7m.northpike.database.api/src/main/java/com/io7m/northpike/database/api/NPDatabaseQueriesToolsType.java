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

import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolExecutionIdentifier;

import java.util.Optional;

/**
 * The database queries involving tools.
 */

public sealed interface NPDatabaseQueriesToolsType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given tool execution description.
   */

  non-sealed interface PutExecutionDescriptionType
    extends NPDatabaseQueryType<NPToolExecutionDescription, NPDatabaseUnit>,
    NPDatabaseQueriesToolsType
  {

  }

  /**
   * Retrieve a tool execution description.
   */

  non-sealed interface GetExecutionDescriptionType
    extends NPDatabaseQueryType<NPToolExecutionIdentifier, Optional<NPToolExecutionDescription>>,
    NPDatabaseQueriesToolsType
  {

  }

  /**
   * Search for tool execution descriptions.
   */

  non-sealed interface SearchExecutionDescriptionType
    extends NPDatabaseQueryType<NPToolExecutionDescriptionSearchParameters, NPToolExecutionDescriptionsPagedType>,
    NPDatabaseQueriesToolsType
  {

  }
}
