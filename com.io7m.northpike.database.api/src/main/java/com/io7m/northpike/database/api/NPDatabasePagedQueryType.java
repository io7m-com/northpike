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

import com.io7m.northpike.model.NPPage;

/**
 * The type of paged queries.
 *
 * @param <T> The type of result values
 */

public interface NPDatabasePagedQueryType<T>
{
  /**
   * Get data for the current page.
   *
   * @param transaction The transaction
   *
   * @return A page of results
   *
   * @throws NPDatabaseException On errors
   */

  NPPage<T> pageCurrent(
    NPDatabaseTransactionType transaction)
    throws NPDatabaseException;

  /**
   * Get data for the next page. If the current page is the last page, the
   * function acts as {@link #pageCurrent(NPDatabaseTransactionType)}.
   *
   * @param transaction The transaction
   *
   * @return A page of results
   *
   * @throws NPDatabaseException On errors
   */

  NPPage<T> pageNext(
    NPDatabaseTransactionType transaction)
    throws NPDatabaseException;

  /**
   * Get data for the previous page. If the current page is the first page, the
   * function acts as {@link #pageCurrent(NPDatabaseTransactionType)}.
   *
   * @param transaction The transaction
   *
   * @return A page of results
   *
   * @throws NPDatabaseException On errors
   */

  NPPage<T> pagePrevious(
    NPDatabaseTransactionType transaction)
    throws NPDatabaseException;
}
