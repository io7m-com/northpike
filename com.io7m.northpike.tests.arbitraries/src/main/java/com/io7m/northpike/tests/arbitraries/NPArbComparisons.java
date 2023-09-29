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


package com.io7m.northpike.tests.arbitraries;

import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;

/**
 * Arbitrary comparisons.
 */

public final class NPArbComparisons
{
  private NPArbComparisons()
  {

  }

  /**
   * Exact comparisons.
   *
   * @param values The raw values
   * @param <T>    The type of values
   *
   * @return Arbitraries
   */

  public static <T> Arbitrary<NPComparisonExactType<T>> exact(
    final Arbitrary<T> values)
  {
    return Arbitraries.oneOf(
      Arbitraries.create(NPComparisonExactType.Anything::new),
      values.map(NPComparisonExactType.IsEqualTo::new),
      values.map(NPComparisonExactType.IsNotEqualTo::new)
    );
  }

  /**
   * Fuzzy comparisons.
   *
   * @param values The raw values
   * @param <T>    The type of values
   *
   * @return Arbitraries
   */

  public static <T> Arbitrary<NPComparisonFuzzyType<T>> fuzzy(
    final Arbitrary<T> values)
  {
    return Arbitraries.oneOf(
      Arbitraries.create(NPComparisonFuzzyType.Anything::new),
      values.map(NPComparisonFuzzyType.IsEqualTo::new),
      values.map(NPComparisonFuzzyType.IsNotEqualTo::new),
      values.map(NPComparisonFuzzyType.IsSimilarTo::new),
      values.map(NPComparisonFuzzyType.IsNotSimilarTo::new)
    );
  }
}
