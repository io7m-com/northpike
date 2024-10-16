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


import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStringConstantType;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Context;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.sql.SQLException;
import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static io.opentelemetry.api.trace.SpanKind.INTERNAL;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_SYSTEM;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DbSystemValues.POSTGRESQL;
import static org.jooq.SQLDialect.POSTGRES;

final class NPDatabaseTransaction
  implements NPDatabaseTransactionType
{
  private final CloseBehavior closeBehavior;
  private final NPDatabaseConnection connection;
  private final Span transactionSpan;
  private NPAuditOwnerType owner;

  enum CloseBehavior {
    ON_CLOSE_CLOSE_CONNECTION,
    ON_CLOSE_DO_NOTHING
  }

  NPDatabaseTransaction(
    final CloseBehavior inCloseBehavior,
    final NPDatabaseConnection inConnection,
    final Span inTransactionScope)
  {
    this.closeBehavior =
      Objects.requireNonNull(inCloseBehavior, "inCloseBehavior");
    this.connection =
      Objects.requireNonNull(inConnection, "connection");
    this.transactionSpan =
      Objects.requireNonNull(inTransactionScope, "inMetricsScope");
  }

  /**
   * @return The transaction span for metrics
   */

  public Span span()
  {
    return this.transactionSpan;
  }

  /**
   * Create a new query span for measuring query times.
   *
   * @param name The query name
   *
   * @return The query span
   */

  public Span createQuerySpan(
    final String name)
  {
    return this.tracer()
      .spanBuilder(name)
      .setParent(Context.current().with(this.transactionSpan))
      .setAttribute(DB_SYSTEM, POSTGRESQL)
      .setSpanKind(INTERNAL)
      .startSpan();
  }

  NPDatabaseConnection connection()
  {
    return this.connection;
  }

  void setRole(
    final NPDatabaseRole role)
    throws SQLException
  {
    switch (role) {
      case NORTHPIKE -> {
        try (var st =
               this.connection.connection()
                 .prepareStatement("set role northpike")) {
          st.execute();
        }
      }
      case NORTHPIKE_READ_ONLY -> {
        try (var st =
               this.connection.connection()
                 .prepareStatement("set role northpike_read_only")) {
          st.execute();
        }
      }
      case NONE -> {
        try (var st =
               this.connection.connection()
                 .prepareStatement("set role northpike_none")) {
          st.execute();
        }
      }
    }
  }

  @Override
  public <T extends NPDatabaseQueriesType> T queries(
    final Class<T> qClass)
    throws NPDatabaseException
  {
    final var constructor =
      this.connection.database()
        .queries(qClass);

    if (constructor != null) {
      return (T) constructor.apply(this);
    }

    throw new NPDatabaseException(
      "Unsupported query type: %s".formatted(qClass),
      NPStandardErrorCodes.errorSqlUnsupportedQueryClass(),
      Map.of(),
      Optional.empty()
    );
  }

  public DSLContext createContext()
  {
    final var sqlConnection =
      this.connection.connection();
    final var settings =
      this.connection.database().settings();
    return DSL.using(sqlConnection, POSTGRES, settings);
  }

  @Override
  public void rollback()
    throws NPDatabaseException
  {
    try {
      this.connection.connection().rollback();
      this.connection.database()
        .counterTransactionRollbacks()
        .add(1L);
    } catch (final SQLException e) {
      throw new NPDatabaseException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorSql(),
        Collections.emptySortedMap(),
        Optional.empty()
      );
    }
  }

  @Override
  public void commit()
    throws NPDatabaseException
  {
    try {
      this.connection.connection().commit();
      this.connection.database()
        .counterTransactionCommits()
        .add(1L);
    } catch (final SQLException e) {
      throw new NPDatabaseException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorSql(),
        Collections.emptySortedMap(),
        Optional.empty()
      );
    }
  }

  @Override
  public void close()
    throws NPDatabaseException
  {
    try {
      this.rollback();
    } catch (final Exception e) {
      this.transactionSpan.recordException(e);
      throw e;
    } finally {
      this.transactionSpan.end();

      switch (this.closeBehavior) {
        case ON_CLOSE_CLOSE_CONNECTION -> {
          this.connection.close();
        }
        case ON_CLOSE_DO_NOTHING -> {

        }
      }
    }
  }

  /**
   * @return The metrics tracer
   */

  Tracer tracer()
  {
    return this.connection.database().tracer();
  }

  @Override
  public void setOwner(
    final NPAuditOwnerType newOwner)
  {
    this.owner = Objects.requireNonNull(newOwner, "owner");
  }

  @Override
  public NPAuditOwnerType owner()
  {
    if (this.owner == null) {
      throw new IllegalStateException("No owner ID has been set.");
    }
    return this.owner;
  }

  @Override
  public String toString()
  {
    return "[NPDatabaseTransaction 0x%s]"
      .formatted(Long.toUnsignedString(this.hashCode(), 16));
  }

  public NPDatabaseConnection getConnection()
  {
    return this.connection;
  }

  String localize(
    final NPStringConstantType c,
    final Object... args)
  {
    return this.connection.database()
      .messages()
      .format(c, args);
  }
}
