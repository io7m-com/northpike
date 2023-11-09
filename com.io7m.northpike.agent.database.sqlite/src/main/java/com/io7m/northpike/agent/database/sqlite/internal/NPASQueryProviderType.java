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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueryType;

import java.util.Objects;
import java.util.function.Function;

/**
 * A query provider returns a class under which the query should be
 * registered (the class used as the argument to
 * {@link com.io7m.northpike.agent.database.api.NPAgentDatabaseTransactionType#queries(Class)}),
 * and a function that yields a query when supplied with a transaction.
 */

public interface NPASQueryProviderType
{
  /**
   * @return Information about the query this provider supplies
   */

  Service<?, ?, ?> information();

  /**
   * The query provider information.
   *
   * @param interfaceClass The interface registry class
   * @param constructor    The constructor for the query
   * @param <P>            The type of parameters
   * @param <R>            The type of returned values
   * @param <Q>            The precise query type
   */

  record Service<P, R, Q extends NPAgentDatabaseQueryType<P, R>>(
    Class<Q> interfaceClass,
    Function<NPASTransaction, Q> constructor)
  {
    /**
     * The query provider information.
     */

    public Service
    {
      Objects.requireNonNull(interfaceClass, "interfaceClass");
      Objects.requireNonNull(constructor, "constructor");
    }
  }
}
