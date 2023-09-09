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

import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/**
 * A page of items.
 *
 * @param items           The items
 * @param pageIndex       The page index (starting at 0)
 * @param pageCount       The total page count
 * @param pageFirstOffset The offset of the first item in the list
 * @param <T>             The type of data
 */

public record NPPage<T>(
  List<T> items,
  int pageIndex,
  int pageCount,
  long pageFirstOffset)
{
  /**
   * A page of items.
   *
   * @param items           The items
   * @param pageIndex       The page index (starting at 0)
   * @param pageCount       The total page count
   * @param pageFirstOffset The offset of the first item in the list
   */

  public NPPage
  {
    Objects.requireNonNull(items, "items");
  }

  /**
   * Map {@code f} over the elements of this page.
   *
   * @param f   The function
   * @param <U> The type of results
   *
   * @return A new page
   */

  public <U> NPPage<U> map(
    final Function<T, U> f)
  {
    return new NPPage<>(
      this.items.stream()
        .map(f)
        .toList(),
      this.pageIndex,
      this.pageCount,
      this.pageFirstOffset
    );
  }
}
