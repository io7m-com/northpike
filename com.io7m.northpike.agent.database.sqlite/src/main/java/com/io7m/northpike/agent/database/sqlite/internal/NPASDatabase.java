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


import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseConnectionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueryType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import org.jooq.conf.RenderNameCase;
import org.jooq.conf.Settings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.sqlite.SQLiteDataSource;

import java.sql.Connection;
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
import static io.opentelemetry.semconv.trace.attributes.SemanticAttributes.DbSystemValues.SQLITE;
import static java.lang.Math.max;
import static java.util.Objects.requireNonNullElse;

/**
 * The default postgres server database implementation.
 */

public final class NPASDatabase implements NPAgentDatabaseType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPASDatabase.class);

  private final Map<Class<?>, Function<NPASTransaction, NPAgentDatabaseQueryType<?, ?>>> queries;
  private final Clock clock;
  private final SQLiteDataSource dataSource;
  private final Settings settings;
  private final Tracer tracer;
  private final CloseableCollectionType<NPAgentDatabaseException> resources;
  private final LongCounter transactions;
  private final LongCounter transactionCommits;
  private final LongCounter transactionRollbacks;
  private final ConcurrentLinkedQueue<Long> connectionTimes;
  private final NPTelemetryServiceType telemetry;
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

  public NPASDatabase(
    final NPTelemetryServiceType inTelemetry,
    final NPStrings inStrings,
    final Clock inClock,
    final SQLiteDataSource inDataSource,
    final CloseableCollectionType<NPAgentDatabaseException> inResources)
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

    final var meter =
      this.telemetry.meter();

    this.transactions =
      meter.counterBuilder("northpike_agent_db_transactions")
        .setDescription("The number of completed transactions.")
        .build();

    this.transactionCommits =
      meter.counterBuilder("northpike_agent_db_commits")
        .setDescription("The number of database transaction commits.")
        .build();

    this.transactionRollbacks =
      meter.counterBuilder("northpike_agent_db_rollbacks")
        .setDescription("The number of database transaction rollbacks.")
        .build();

    this.connectionTimes =
      new ConcurrentLinkedQueue<>();

    this.resources.add(
      meter.gaugeBuilder("northpike_agent_db_connection_time")
        .setDescription("The amount of time a database connection is held.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(maxOf(this.connectionTimes));
        })
    );
  }

  @SuppressWarnings("unchecked")
  private static Map<Class<?>, Function<NPASTransaction, NPAgentDatabaseQueryType<?, ?>>> loadQueryProviders()
  {
    final var loader =
      ServiceLoader.load(NPASQueryProviderType.class);
    final var iterator =
      loader.iterator();

    final var providers =
      new HashMap<
        Class<?>,
        Function<NPASTransaction, NPAgentDatabaseQueryType<?, ?>>>();

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
        (Function<NPASTransaction, NPAgentDatabaseQueryType<?, ?>>) information.constructor()
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
    throws NPAgentDatabaseException
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
  public NPAgentDatabaseConnectionType openConnection()
    throws NPAgentDatabaseException
  {
    final var span =
      this.tracer
        .spanBuilder("NPAgentDatabaseConnection")
        .setSpanKind(SpanKind.SERVER)
        .setAttribute(DB_SYSTEM, SQLITE)
        .startSpan();

    try {
      span.addEvent("RequestConnection");
      final var conn = this.dataSource.getConnection();
      span.addEvent("ObtainedConnection");
      span.addEvent("RequestWALMode");
      setWALMode(conn);
      span.addEvent("ObtainedWALMode");

      final var timeNow = OffsetDateTime.now();
      conn.setAutoCommit(false);

      return new NPASConnection(this, conn, timeNow, span);
    } catch (final SQLException e) {
      span.recordException(e);
      span.end();

      throw new NPAgentDatabaseException(
        requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
        e,
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  private static void setWALMode(
    final Connection connection)
    throws SQLException
  {
    try (var st = connection.createStatement()) {
      st.execute("PRAGMA journal_mode=WAL;");
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
    return "[NPAgentDatabase 0x%s]"
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

  Function<NPASTransaction, NPAgentDatabaseQueryType<?, ?>> queries(
    final Class<?> qClass)
  {
    return this.queries.get(qClass);
  }
}
