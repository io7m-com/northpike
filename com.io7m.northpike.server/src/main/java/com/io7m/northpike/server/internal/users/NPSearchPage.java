/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.server.internal.users;

/**
 * An immutable search page.
 *
 * @param pageIndex  The page index
 * @param pageSize   The page size
 * @param pageCount  The page count
 * @param itemOffset The item offset for this page
 * @param itemTotal  The total number of items
 */

public record NPSearchPage(
  long pageIndex,
  long pageSize,
  long pageCount,
  long itemOffset,
  long itemTotal)
{
  /**
   * @return The next page (or this page, if we're on the last page)
   */

  public NPSearchPage next()
  {
    if (this.pageIndex == this.pageCount) {
      return this;
    }
    return new NPSearchPage(
      this.pageIndex + 1L,
      this.pageSize,
      this.pageCount,
      this.itemOffset + this.pageSize,
      this.itemTotal
    );
  }

  /**
   * @return The previous page (or this page, if we're on the first page)
   */

  public NPSearchPage previous()
  {
    if (this.pageIndex == 1L) {
      return this;
    }
    return new NPSearchPage(
      this.pageIndex - 1L,
      this.pageSize,
      this.pageCount,
      this.itemOffset - this.pageSize,
      this.itemTotal
    );
  }
}
