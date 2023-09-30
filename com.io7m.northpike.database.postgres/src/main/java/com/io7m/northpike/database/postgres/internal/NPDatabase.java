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


import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueryType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTelemetry;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStrings;
import com.zaxxer.hikari.HikariDataSource;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import org.jooq.conf.RenderNameCase;
import org.jooq.conf.Settings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.sql.SQLException;
import java.time.Clock;
import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.ServiceLoader;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.Function;

import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DB_SYSTEM;
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DbSystemValues.POSTGRESQL;
import static java.lang.Math.max;
import static java.util.Objects.requireNonNullElse;

/**
 * The default postgres server database implementation.
 */

public final class NPDatabase implements NPDatabaseType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabase.class);

  private final Map<Class<?>, Function<NPDatabaseTransaction, NPDatabaseQueryType<?, ?>>> queries;
  private final Clock clock;
  private final HikariDataSource dataSource;
  private final Settings settings;
  private final Tracer tracer;
  private final CloseableCollectionType<NPDatabaseException> resources;
  private final LongCounter transactions;
  private final LongCounter transactionCommits;
  private final LongCounter transactionRollbacks;
  private final ConcurrentLinkedQueue<Long> connectionTimes;
  private final NPDatabaseTelemetry telemetry;
  private final NPStrings strings;

  /**
   * The default postgres server database implementation.
   *
   * @param inStrings    The string resources
   * @param inTelemetry  A telemetry
   * @param inClock      The clock
   * @param inDataSource A pooled data source
   * @param inResources  The resources to be closed
   */

  public NPDatabase(
    final NPDatabaseTelemetry inTelemetry,
    final NPStrings inStrings,
    final Clock inClock,
    final HikariDataSource inDataSource,
    final CloseableCollectionType<NPDatabaseException> inResources)
  {
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.strings =
      Objects.requireNonNull(inStrings, "inStrings");
    this.tracer =
      this.telemetry.tracer();
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.dataSource =
      Objects.requireNonNull(inDataSource, "dataSource");
    this.queries =
      loadQueryProviders();

    this.settings =
      new Settings()
        .withRenderNameCase(RenderNameCase.LOWER);

    final var dataSourceBean =
      this.dataSource.getHikariPoolMXBean();
    final var meter =
      this.telemetry.meter();

    this.transactions =
      meter.counterBuilder("northpike_db_transactions")
        .setDescription("The number of completed transactions.")
        .build();

    this.transactionCommits =
      meter.counterBuilder("northpike_db_commits")
        .setDescription("The number of database transaction commits.")
        .build();

    this.transactionRollbacks =
      meter.counterBuilder("northpike_db_rollbacks")
        .setDescription("The number of database transaction rollbacks.")
        .build();

    this.connectionTimes =
      new ConcurrentLinkedQueue<>();

    this.resources.add(
      meter.gaugeBuilder("northpike_db_connection_time")
        .setDescription("The amount of time a database connection is held.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(maxOf(this.connectionTimes));
        })
    );

    this.resources.add(
      meter.gaugeBuilder("northpike_db_connections_active")
        .setDescription("Number of active database connections.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(
            Integer.toUnsignedLong(dataSourceBean.getActiveConnections())
          );
        })
    );

    this.resources.add(
      meter.gaugeBuilder("northpike_db_connections_idle")
        .setDescription("Number of idle database connections.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(
            Integer.toUnsignedLong(dataSourceBean.getIdleConnections())
          );
        })
    );

    this.resources.add(
      meter.gaugeBuilder("northpike_db_connections_total")
        .setDescription("Total number of database connections.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(
            Integer.toUnsignedLong(dataSourceBean.getTotalConnections())
          );
        })
    );

    this.resources.add(
      meter.gaugeBuilder("northpike_db_threads_waiting")
        .setDescription("Number of threads waiting for connections.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(
            Integer.toUnsignedLong(dataSourceBean.getThreadsAwaitingConnection())
          );
        })
    );
  }

  @SuppressWarnings("unchecked")
  private static Map<Class<?>, Function<NPDatabaseTransaction, NPDatabaseQueryType<?, ?>>> loadQueryProviders()
  {
    final var loader =
      ServiceLoader.load(NPDBQueryProviderType.class);
    final var iterator =
      loader.iterator();

    final var providers =
      new HashMap<
        Class<?>,
        Function<NPDatabaseTransaction, NPDatabaseQueryType<?, ?>>>();

    while (iterator.hasNext()) {
      final var provider =
        iterator.next();
      final var information =
        provider.information();

      final var interfaceClass =
        information.interfaceClass();

      LOG.debug("Loaded query {}", interfaceClass.getCanonicalName());

      if (providers.containsKey(interfaceClass)) {
        final var builder = new StringBuilder(128);
        builder.append("Query interface class registered multiple times.");
        builder.append(System.lineSeparator());
        builder.append(" Provider: ");
        builder.append(provider.getClass());
        builder.append(System.lineSeparator());
        builder.append(" Interface: ");
        builder.append(interfaceClass);
        builder.append(System.lineSeparator());
        throw new IllegalStateException(builder.toString());
      }

      providers.put(
        interfaceClass,
        (Function<NPDatabaseTransaction, NPDatabaseQueryType<?, ?>>) information.constructor()
      );
    }

    return Map.copyOf(providers);
  }

  private static long maxOf(
    final ConcurrentLinkedQueue<Long> times)
  {
    var time = 0L;
    while (!times.isEmpty()) {
      time = max(time, times.poll().longValue());
    }
    return time;
  }

  LongCounter counterTransactions()
  {
    return this.transactions;
  }

  LongCounter counterTransactionCommits()
  {
    return this.transactionCommits;
  }

  LongCounter counterTransactionRollbacks()
  {
    return this.transactionRollbacks;
  }

  @Override
  public void close()
    throws NPDatabaseException
  {
    this.resources.close();
  }

  /**
   * @return The OpenTelemetry tracer
   */

  public Tracer tracer()
  {
    return this.tracer;
  }

  @Override
  public NPDatabaseConnectionType openConnection(
    final NPDatabaseRole role)
    throws NPDatabaseException
  {
    final var span =
      this.tracer
        .spanBuilder("NPDatabaseConnection")
        .setSpanKind(SpanKind.SERVER)
        .setAttribute(DB_SYSTEM, POSTGRESQL)
        .startSpan();

    try {
      span.addEvent("RequestConnection");
      final var conn = this.dataSource.getConnection();
      span.addEvent("ObtainedConnection");
      final var timeNow = OffsetDateTime.now();
      conn.setAutoCommit(false);
      return new NPDatabaseConnection(this, conn, timeNow, role, span);
    } catch (final SQLException e) {
      span.recordException(e);
      span.end();

      throw new NPDatabaseException(
        requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
        e,
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  /**
   * @return The jooq SQL settings
   */

  Settings settings()
  {
    return this.settings;
  }

  /**
   * @return The clock used for time-related queries
   */

  Clock clock()
  {
    return this.clock;
  }

  @Override
  public String description()
  {
    return "Server database service.";
  }

  @Override
  public String toString()
  {
    return "[NPDatabase 0x%s]"
      .formatted(Long.toUnsignedString(this.hashCode(), 16));
  }

  void setConnectionTimeNow(
    final long nanos)
  {
    if (!this.telemetry.isNoOp()) {
      this.connectionTimes.add(Long.valueOf(nanos));
    }
  }

  NPStrings messages()
  {
    return this.strings;
  }

  /**
   * Find a query registered with the given class.
   *
   * @param qClass The class
   *
   * @return A query
   */

  Function<NPDatabaseTransaction, NPDatabaseQueryType<?, ?>> queries(
    final Class<?> qClass)
  {
    return this.queries.get(qClass);
  }
}
