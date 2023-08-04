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


package com.io7m.northpike.database.postgres.internal;

import com.io7m.northpike.database.postgres.internal.NPDBMatch.QuerySetType.QuerySetCondition;
import com.io7m.northpike.database.postgres.internal.NPDBMatch.QuerySetType.QuerySetIntersection;
import com.io7m.northpike.database.postgres.internal.NPDBMatch.QuerySetType.QuerySetUnion;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import org.jooq.Condition;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;

/**
 * Functions to transform match expressions to database queries.
 */

public final class NPDBMatch
{
  private NPDBMatch()
  {

  }

  /**
   * A set of queries.
   */

  sealed interface QuerySetType
  {
    /**
     * A simple query handled with a WHERE clause.
     *
     * @param condition The condition
     */

    record QuerySetCondition(
      Condition condition)
      implements QuerySetType
    {

    }

    /**
     * A pair of queries that are combined with a set union.
     *
     * @param q0 The left query
     * @param q1 The right query
     */

    record QuerySetUnion(
      QuerySetType q0,
      QuerySetType q1)
      implements QuerySetType
    {

    }

    /**
     * A pair of queries that are combined with a set intersection.
     *
     * @param q0 The left query
     * @param q1 The right query
     */

    record QuerySetIntersection(
      QuerySetType q0,
      QuerySetType q1)
      implements QuerySetType
    {

    }
  }

  static QuerySetType ofAgentLabelMatch(
    final NPAgentLabelMatchType match)
  {
    if (match instanceof final NPAgentLabelMatchType.And and) {
      return new QuerySetIntersection(
        ofAgentLabelMatch(and.e0()),
        ofAgentLabelMatch(and.e1())
      );
    }

    if (match instanceof final NPAgentLabelMatchType.Or or) {
      return new QuerySetUnion(
        ofAgentLabelMatch(or.e0()),
        ofAgentLabelMatch(or.e1())
      );
    }

    if (match instanceof NPAgentLabelMatchType.AnyLabel) {
      return new QuerySetCondition(DSL.trueCondition());
    }

    if (match instanceof final NPAgentLabelMatchType.Specific sp) {
      return new QuerySetCondition(
        AGENT_LABEL_DEFINITIONS.ALD_NAME.eq(sp.name().value())
      );
    }

    throw new IllegalStateException();
  }
}
