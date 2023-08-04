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

package com.io7m.northpike.model;

import com.io7m.lanark.core.RDottedName;

import java.util.Objects;

/**
 * An expression that matches labels on an agent.
 */

public sealed interface NPAgentLabelMatchType
{
  /**
   * An expression that matches any label.
   */

  enum AnyLabel implements NPAgentLabelMatchType
  {
    /**
     * An expression that matches any label.
     */

    ANY_LABEL
  }

  /**
   * The conjunction of {@code e0} and {@code e1}. The resulting set of
   * labels is the intersection of those matched by both
   * {@code e0} and {@code e1}.
   *
   * @param e0 The left match expression
   * @param e1 The right match expression
   */

  record And(
    NPAgentLabelMatchType e0,
    NPAgentLabelMatchType e1)
    implements NPAgentLabelMatchType
  {
    /**
     * The conjunction of {@code e0} and {@code e1}. The resulting set of
     * labels is the intersection of those matched by both
     * {@code e0} and {@code e1}.
     */

    public And
    {
      Objects.requireNonNull(e0, "e0");
      Objects.requireNonNull(e1, "e1");
    }
  }

  /**
   * The disjunction of {@code e0} and {@code e1}. The resulting set of
   * labels is the union of those matched by {@code e0} or {@code e1}.
   *
   * @param e0 The left match expression
   * @param e1 The right match expression
   */

  record Or(
    NPAgentLabelMatchType e0,
    NPAgentLabelMatchType e1)
    implements NPAgentLabelMatchType
  {
    /**
     * The disjunction of {@code e0} and {@code e1}. The resulting set of
     * labels is the union of those matched by {@code e0} or {@code e1}.
     */

    public Or
    {
      Objects.requireNonNull(e0, "e0");
      Objects.requireNonNull(e1, "e1");
    }
  }

  /**
   * Match a specific label.
   *
   * @param name The label name
   */

  record Specific(RDottedName name)
    implements NPAgentLabelMatchType
  {
    /**
     * Match a specific label.
     */

    public Specific
    {
      Objects.requireNonNull(name, "name");
    }
  }
}
