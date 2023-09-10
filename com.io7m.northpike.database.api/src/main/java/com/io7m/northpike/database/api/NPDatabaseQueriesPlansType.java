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


import com.io7m.northpike.plans.NPPlanDescription;
import com.io7m.northpike.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanSearchParameters;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;

import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The database queries involving plans.
 */

public sealed interface NPDatabaseQueriesPlansType
  extends NPDatabaseQueriesType
{
  /**
   * Update the given plan.
   */

  non-sealed interface PutType
    extends NPDatabaseQueryType<PutType.Parameters, NPDatabaseUnit>,
    NPDatabaseQueriesPlansType
  {
    /**
     * Update the given plan.
     *
     * @param plan        The plan
     * @param serializers The serializers
     */

    record Parameters(
      NPPlanType plan,
      NPPlanSerializerFactoryType serializers)
    {
      /**
       * Update the given plan.
       */

      public Parameters
      {
        Objects.requireNonNull(plan, "identifier");
        Objects.requireNonNull(serializers, "parsers");
      }
    }
  }

  /**
   * Retrieve a plan.
   */

  non-sealed interface GetType
    extends NPDatabaseQueryType<GetType.Parameters, Optional<NPPlanDescription>>,
    NPDatabaseQueriesPlansType
  {
    /**
     * Retrieve a plan.
     *
     * @param identifier The identifier
     * @param parsers    The parsers
     */

    record Parameters(
      NPPlanIdentifier identifier,
      Set<NPPlanParserFactoryType> parsers)
    {
      /**
       * Retrieve a plan.
       */

      public Parameters
      {
        Objects.requireNonNull(identifier, "identifier");
        Objects.requireNonNull(parsers, "parsers");
      }
    }
  }

  /**
   * Retrieve the raw text of a plan.
   */

  non-sealed interface GetUnparsedType
    extends NPDatabaseQueryType<NPPlanIdentifier, Optional<NPPlanDescriptionUnparsed>>,
    NPDatabaseQueriesPlansType
  {

  }

  /**
   * Search for plans.
   */

  non-sealed interface SearchType
    extends NPDatabaseQueryType<NPPlanSearchParameters, NPPlansPagedType>,
    NPDatabaseQueriesPlansType
  {

  }
}
