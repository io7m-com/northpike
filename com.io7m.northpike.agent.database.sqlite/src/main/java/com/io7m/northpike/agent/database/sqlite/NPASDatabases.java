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

package com.io7m.northpike.agent.database.sqlite;

import com.io7m.anethum.api.ParsingException;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseCreate;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseFactoryType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.database.sqlite.internal.NPASDatabase;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.trasco.api.TrArguments;
import com.io7m.trasco.api.TrEventExecutingSQL;
import com.io7m.trasco.api.TrEventType;
import com.io7m.trasco.api.TrEventUpgrading;
import com.io7m.trasco.api.TrException;
import com.io7m.trasco.api.TrExecutorConfiguration;
import com.io7m.trasco.api.TrSchemaRevisionSet;
import com.io7m.trasco.vanilla.TrExecutors;
import com.io7m.trasco.vanilla.TrSchemaRevisionSetParsers;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.sqlite.SQLiteConfig;
import org.sqlite.SQLiteDataSource;
import org.sqlite.SQLiteErrorCode;
import org.sqlite.SQLiteOpenMode;

import java.io.IOException;
import java.math.BigInteger;
import java.net.URI;
import java.sql.Connection;
import java.sql.SQLException;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;

import static com.io7m.trasco.api.TrExecutorUpgrade.FAIL_INSTEAD_OF_UPGRADING;
import static com.io7m.trasco.api.TrExecutorUpgrade.PERFORM_UPGRADES;
import static java.math.BigInteger.valueOf;
import static java.util.Objects.requireNonNullElse;

/**
 * The default SQLite server database implementation.
 */

public final class NPASDatabases implements NPAgentDatabaseFactoryType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPASDatabases.class);

  private static final String DATABASE_APPLICATION_ID =
    "com.io7m.northpike";

  /**
   * The default postgres server database implementation.
   */

  public NPASDatabases()
  {

  }

  private static void schemaVersionSet(
    final BigInteger version,
    final Connection connection)
    throws SQLException
  {
    final String statementText;
    if (Objects.equals(version, BigInteger.ZERO)) {
      statementText = "insert into schema_version (version_application_id, version_number) values (?, ?)";
      try (var statement =
             connection.prepareStatement(statementText)) {
        statement.setString(1, DATABASE_APPLICATION_ID);
        statement.setLong(2, version.longValueExact());
        statement.execute();
      }
    } else {
      statementText = "update schema_version set version_number = ?";
      try (var statement =
             connection.prepareStatement(statementText)) {
        statement.setLong(1, version.longValueExact());
        statement.execute();
      }
    }
  }

  private static Optional<BigInteger> schemaVersionGet(
    final Connection connection)
    throws SQLException
  {
    Objects.requireNonNull(connection, "connection");

    try {
      final var statementText =
        "SELECT version_application_id, version_number FROM schema_version";
      LOG.debug("execute: {}", statementText);

      try (var statement = connection.prepareStatement(statementText)) {
        try (var result = statement.executeQuery()) {
          if (!result.next()) {
            throw new SQLException("schema_version table is empty!");
          }
          final var applicationCA =
            result.getString(1);
          final var version =
            result.getLong(2);

          if (!Objects.equals(applicationCA, DATABASE_APPLICATION_ID)) {
            throw new SQLException(
              String.format(
                "Database application ID is %s but should be %s",
                applicationCA,
                DATABASE_APPLICATION_ID
              )
            );
          }

          return Optional.of(valueOf(version));
        }
      }
    } catch (final SQLException e) {
      if (e.getErrorCode() == SQLiteErrorCode.SQLITE_ERROR.code) {
        connection.rollback();
        return Optional.empty();
      }
      throw e;
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

  @Override
  public String kind()
  {
    return "SQLITE";
  }

  @Override
  public NPAgentDatabaseType open(
    final NPAgentDatabaseSetup setup,
    final Consumer<String> startupMessages)
    throws NPAgentDatabaseException
  {
    Objects.requireNonNull(setup, "setup");
    Objects.requireNonNull(startupMessages, "startupMessages");

    createOrUpgrade(setup, startupMessages);
    return connect(setup);
  }

  private static NPAgentDatabaseType connect(
    final NPAgentDatabaseSetup setup)
  {
    final var resources = CloseableCollection.create(() -> {
      return new NPAgentDatabaseException(
        "Closing a resource failed.",
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    });

    final var url = new StringBuilder(128);
    url.append("jdbc:sqlite:");
    url.append(setup.configuration().databaseFile());

    final var config = new SQLiteConfig();
    config.setApplicationId(0x50494b45);
    config.enforceForeignKeys(true);

    final var dataSource = new SQLiteDataSource(config);
    dataSource.setUrl(url.toString());

    return new NPASDatabase(
      setup.telemetry(),
      setup.strings(),
      setup.clock(),
      dataSource,
      resources
    );
  }

  private static void createOrUpgrade(
    final NPAgentDatabaseSetup setup,
    final Consumer<String> startupMessages)
    throws NPAgentDatabaseException
  {
    final var resources = CloseableCollection.create(() -> {
      return new NPAgentDatabaseException(
        "Closing a resource failed.",
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    });

    final var span =
      setup.telemetry()
        .tracer()
        .spanBuilder("DatabaseSetup")
        .startSpan();

    final var arguments =
      new TrArguments(Map.of());

    try (var ignored0 = span.makeCurrent()) {
      try (var ignored1 = resources) {
        final var url = new StringBuilder(128);
        url.append("jdbc:sqlite:");
        url.append(setup.configuration().databaseFile());

        final var config = new SQLiteConfig();
        config.setApplicationId(0x50494b45);
        config.enforceForeignKeys(true);

        if (setup.configuration().create() == NPAgentDatabaseCreate.CREATE_DATABASE) {
          config.setOpenMode(SQLiteOpenMode.CREATE);
        } else {
          config.resetOpenMode(SQLiteOpenMode.CREATE);
        }

        final var dataSource = new SQLiteDataSource(config);
        dataSource.setUrl(url.toString());

        final var parsers = new TrSchemaRevisionSetParsers();
        final TrSchemaRevisionSet revisions;
        try (var stream = NPASDatabases.class.getResourceAsStream(
          "/com/io7m/northpike/database/sqlite/internal/database.xml")) {
          revisions = parsers.parse(URI.create("urn:source"), stream);
        }

        try (var connection = dataSource.getConnection()) {
          setWALMode(connection);
          connection.setAutoCommit(false);

          new TrExecutors().create(
            new TrExecutorConfiguration(
              NPASDatabases::schemaVersionGet,
              NPASDatabases::schemaVersionSet,
              event -> publishTrEvent(startupMessages, event),
              revisions,
              switch (setup.configuration().upgrade()) {
                case UPGRADE_DATABASE -> PERFORM_UPGRADES;
                case DO_NOT_UPGRADE_DATABASE -> FAIL_INSTEAD_OF_UPGRADING;
              },
              arguments,
              connection
            )
          ).execute();
          connection.commit();
        }
      } catch (final IOException e) {
        failSpan(e);
        throw new NPAgentDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorIo(),
          Map.of(),
          Optional.empty()
        );
      } catch (final TrException e) {
        failSpan(e);
        throw new NPAgentDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorTrasco(),
          Map.of(),
          Optional.empty()
        );
      } catch (final ParsingException e) {
        failSpan(e);
        throw new NPAgentDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorSqlRevision(),
          Map.of(),
          Optional.empty()
        );
      } catch (final SQLException e) {
        failSpan(e);
        throw new NPAgentDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorSql(),
          Map.of(),
          Optional.empty()
        );
      }
    }
  }

  private static void failSpan(
    final Exception e)
  {
    final Span span = Span.current();
    span.recordException(e);
    span.setStatus(StatusCode.ERROR);
  }

  private static void publishEvent(
    final Consumer<String> startupMessages,
    final String message)
  {
    try {
      LOG.trace("{}", message);
      startupMessages.accept(message);

      final var span = Span.current();
      span.addEvent(message);
    } catch (final Exception e) {
      LOG.error("ignored consumer exception: ", e);
    }
  }

  private static void publishTrEvent(
    final Consumer<String> startupMessages,
    final TrEventType event)
  {
    switch (event) {
      case final TrEventExecutingSQL sql -> {
        publishEvent(
          startupMessages,
          String.format("Executing SQL: %s", sql.statement())
        );
        return;
      }
      case final TrEventUpgrading upgrading -> {
        publishEvent(
          startupMessages,
          String.format(
            "Upgrading database from version %s -> %s",
            upgrading.fromVersion(),
            upgrading.toVersion())
        );
        return;
      }
    }
  }
}
