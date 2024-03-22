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

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueryType;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import org.jooq.DSLContext;
import org.jooq.Query;
import org.jooq.exception.DataAccessException;

import java.time.OffsetDateTime;
import java.util.Collection;
import java.util.Map;
import java.util.Objects;
import java.util.TreeMap;
import java.util.stream.Collectors;

import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_STATEMENT;

abstract class NPASQAbstract<P, R>
  implements NPAgentDatabaseQueryType<P, R>
{
  private final NPASTransaction transaction;
  private final TreeMap<String, String> attributes;

  protected NPASQAbstract(
    final NPASTransaction inTransaction)
  {
    this.transaction =
      Objects.requireNonNull(inTransaction, "transaction");
    this.attributes =
      new TreeMap<String, String>();
  }

  private static void recordQueryText(
    final String queryText)
  {
    Span.current().setAttribute(DB_STATEMENT, queryText);
  }

  protected static void recordQuery(
    final Query query)
  {
    recordQueryText(query.toString());
  }

  protected static void recordQuery(
    final Collection<Query> queries)
  {
    recordQueryText(
      queries.stream()
        .map(Object::toString)
        .collect(Collectors.joining(";\n\n"))
    );
  }

  protected final Span transactionSpan()
  {
    return this.transaction.span();
  }

  protected final NPASTransaction transaction()
  {
    return this.transaction;
  }

  private NPStrings messages()
  {
    return this.transaction.connection()
      .database()
      .messages();
  }

  protected final String local(
    final NPStringConstantType constant)
  {
    return this.messages().format(constant);
  }

  protected final void setAttribute(
    final NPStringConstantType name,
    final String value)
  {
    this.attributes.put(this.local(name), value);
  }

  @Override
  public final R execute(
    final P parameters)
    throws NPAgentDatabaseException
  {
    Objects.requireNonNull(parameters, "parameters");

    final var currentTransaction =
      this.transaction();
    final var context =
      currentTransaction.createContext();
    final var querySpan =
      currentTransaction.createQuerySpan(this.getClass().getSimpleName());

    try (var ignored = querySpan.makeCurrent()) {
      return this.onExecute(context, parameters);
    } catch (final DataAccessException e) {
      querySpan.recordException(e);
      querySpan.setStatus(StatusCode.ERROR);
      throw NPASExceptions.handleDatabaseException(
        currentTransaction,
        e,
        this.attributes
      );
    } finally {
      querySpan.end();
    }
  }

  protected abstract R onExecute(
    DSLContext context,
    P parameters)
    throws NPAgentDatabaseException;

  protected final Map<String, String> attributes()
  {
    return this.attributes;
  }

  protected final OffsetDateTime timeNow()
  {
    return OffsetDateTime.now(
      this.transaction.connection()
        .database()
        .clock()
    );
  }
}
