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

import com.io7m.northpike.model.NPAuditUserOrAgentType;

/**
 * A database transaction. If the transaction is closed, it is automatically
 * rolled back.
 */

public interface NPDatabaseTransactionType extends AutoCloseable
{
  @Override
  void close()
    throws NPDatabaseException;

  /**
   * Obtain queries for the transaction.
   *
   * @param queryClass The query type
   * @param <T>        The query type
   *
   * @return Queries
   *
   * @throws NPDatabaseException On errors
   */

  <T extends NPDatabaseQueriesType> T queries(Class<T> queryClass)
    throws NPDatabaseException;

  /**
   * Roll back the transaction.
   *
   * @throws NPDatabaseException On errors
   */

  void rollback()
    throws NPDatabaseException;

  /**
   * Commit the transaction.
   *
   * @throws NPDatabaseException On errors
   */

  void commit()
    throws NPDatabaseException;

  /**
   * Set the transaction's owner ID.
   *
   * @param newOwner The owner ID
   */

  void setOwner(
    NPAuditUserOrAgentType newOwner);

  /**
   * @return The transaction's owner ID
   */

  NPAuditUserOrAgentType owner();
}
