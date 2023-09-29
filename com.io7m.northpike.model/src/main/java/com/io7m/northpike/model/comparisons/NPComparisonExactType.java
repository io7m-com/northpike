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


package com.io7m.northpike.model.comparisons;

import java.util.Objects;

/**
 * The type of expressions that can only match values exactly.
 *
 * @param <T> The type of values
 */

public sealed interface NPComparisonExactType<T>
  extends NPComparisonType
{
  /**
   * Match any value.
   *
   * @param <T> The type of values
   */

  record Anything<T>() implements NPComparisonExactType<T>
  {

  }

  /**
   * Match a value exactly.
   *
   * @param value The value
   * @param <T>   The type of values
   */

  record IsEqualTo<T>(T value)
    implements NPComparisonExactType<T>
  {
    /**
     * Match a value exactly.
     */

    public IsEqualTo
    {
      Objects.requireNonNull(value, "value");
    }
  }

  /**
   * Match a value exactly.
   *
   * @param value The value
   * @param <T>   The type of values
   */

  record IsNotEqualTo<T>(T value)
    implements NPComparisonExactType<T>
  {
    /**
     * Match a value exactly.
     */

    public IsNotEqualTo
    {
      Objects.requireNonNull(value, "value");
    }
  }
}
