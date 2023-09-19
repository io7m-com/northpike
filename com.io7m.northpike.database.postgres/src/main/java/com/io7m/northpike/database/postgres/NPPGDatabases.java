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

package com.io7m.northpike.database.postgres;

import com.io7m.anethum.api.ParsingException;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseFactoryType;
import com.io7m.northpike.database.api.NPDatabaseTelemetry;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.postgres.internal.NPDatabase;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.trasco.api.TrArgumentString;
import com.io7m.trasco.api.TrArguments;
import com.io7m.trasco.api.TrEventExecutingSQL;
import com.io7m.trasco.api.TrEventType;
import com.io7m.trasco.api.TrEventUpgrading;
import com.io7m.trasco.api.TrException;
import com.io7m.trasco.api.TrExecutorConfiguration;
import com.io7m.trasco.api.TrSchemaRevisionSet;
import com.io7m.trasco.vanilla.TrExecutors;
import com.io7m.trasco.vanilla.TrSchemaRevisionSetParsers;
import com.zaxxer.hikari.HikariConfig;
import com.zaxxer.hikari.HikariDataSource;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import org.jooq.conf.RenderNameCase;
import org.jooq.conf.Settings;
import org.jooq.impl.DSL;
import org.postgresql.util.PSQLState;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
import static org.jooq.SQLDialect.POSTGRES;

/**
 * The default postgres server database implementation.
 */

public final class NPPGDatabases implements NPDatabaseFactoryType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPPGDatabases.class);

  private static final String DATABASE_APPLICATION_ID =
    "com.io7m.northpike";

  /**
   * The default postgres server database implementation.
   */

  public NPPGDatabases()
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
      final var state = e.getSQLState();
      if (state == null) {
        throw e;
      }
      if (state.equals(PSQLState.UNDEFINED_TABLE.getState())) {
        connection.rollback();
        return Optional.empty();
      }

      throw e;
    }
  }

  @Override
  public String kind()
  {
    return "POSTGRESQL";
  }

  @Override
  public NPDatabaseType open(
    final NPDatabaseConfiguration configuration,
    final NPDatabaseTelemetry telemetry,
    final Consumer<String> startupMessages)
    throws NPDatabaseException
  {
    Objects.requireNonNull(configuration, "configuration");
    Objects.requireNonNull(telemetry, "telemetry");
    Objects.requireNonNull(startupMessages, "startupMessages");

    createOrUpgrade(telemetry, configuration, startupMessages);
    return connect(telemetry, configuration);
  }

  private static NPDatabaseType connect(
    final NPDatabaseTelemetry telemetry,
    final NPDatabaseConfiguration configuration)
  {
    final var resources = CloseableCollection.create(() -> {
      return new NPDatabaseException(
        "Closing a resource failed.",
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    });

    final var url = new StringBuilder(128);
    url.append("jdbc:postgresql://");
    url.append(configuration.address());
    url.append(':');
    url.append(configuration.port());
    url.append('/');
    url.append(configuration.databaseName());
    url.append("?ssl=");
    url.append(configuration.useTLS());

    final var config = new HikariConfig();
    config.setJdbcUrl(url.toString());
    config.setUsername("northpike");
    config.setPassword(configuration.workerRolePassword());
    config.setAutoCommit(false);

    final var dataSource =
      resources.add(new HikariDataSource(config));

    return new NPDatabase(
      telemetry,
      configuration.strings(),
      configuration.clock(),
      dataSource,
      resources
    );
  }

  private static void createOrUpgrade(
    final NPDatabaseTelemetry telemetry,
    final NPDatabaseConfiguration configuration,
    final Consumer<String> startupMessages)
    throws NPDatabaseException
  {
    final var resources = CloseableCollection.create(() -> {
      return new NPDatabaseException(
        "Closing a resource failed.",
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    });

    final var span =
      telemetry.tracer()
        .spanBuilder("DatabaseSetup")
        .startSpan();

    final var argSearchLanguage =
      new TrArgumentString("search.language", configuration.language());

    final var arguments =
      new TrArguments(
        Map.ofEntries(
          Map.entry(argSearchLanguage.name(), argSearchLanguage)
        )
      );

    try (var ignored0 = span.makeCurrent()) {
      try (var ignored1 = resources) {
        final var url = new StringBuilder(128);
        url.append("jdbc:postgresql://");
        url.append(configuration.address());
        url.append(':');
        url.append(configuration.port());
        url.append('/');
        url.append(configuration.databaseName());

        final var config = new HikariConfig();
        config.setJdbcUrl(url.toString());
        config.setUsername(configuration.ownerRoleName());
        config.setPassword(configuration.ownerRolePassword());
        config.setAutoCommit(false);

        final var dataSource =
          resources.add(new HikariDataSource(config));

        final var parsers = new TrSchemaRevisionSetParsers();
        final TrSchemaRevisionSet revisions;
        try (var stream = NPPGDatabases.class.getResourceAsStream(
          "/com/io7m/northpike/database/postgres/internal/database.xml")) {
          revisions = parsers.parse(URI.create("urn:source"), stream);
        }

        try (var connection = dataSource.getConnection()) {
          connection.setAutoCommit(false);

          new TrExecutors().create(
            new TrExecutorConfiguration(
              NPPGDatabases::schemaVersionGet,
              NPPGDatabases::schemaVersionSet,
              event -> publishTrEvent(startupMessages, event),
              revisions,
              switch (configuration.upgrade()) {
                case UPGRADE_DATABASE -> PERFORM_UPGRADES;
                case DO_NOT_UPGRADE_DATABASE -> FAIL_INSTEAD_OF_UPGRADING;
              },
              arguments,
              connection
            )
          ).execute();

          updateWorkerRolePassword(configuration, connection);
          updateReadOnlyRolePassword(configuration, connection);
          connection.commit();
        }
      } catch (final IOException e) {
        failSpan(e);
        throw new NPDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorIo(),
          Map.of(),
          Optional.empty()
        );
      } catch (final TrException e) {
        failSpan(e);
        throw new NPDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorTrasco(),
          Map.of(),
          Optional.empty()
        );
      } catch (final ParsingException e) {
        failSpan(e);
        throw new NPDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorSqlRevision(),
          Map.of(),
          Optional.empty()
        );
      } catch (final SQLException e) {
        failSpan(e);
        throw new NPDatabaseException(
          requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
          e,
          NPStandardErrorCodes.errorSql(),
          Map.of(),
          Optional.empty()
        );
      }
    }
  }

  /**
   * Update the read-only role password. If no password is specified, then
   * logging in is prevented.
   */

  private static void updateReadOnlyRolePassword(
    final NPDatabaseConfiguration configuration,
    final Connection connection)
    throws SQLException
  {
    final var passwordOpt = configuration.readerRolePassword();
    if (passwordOpt.isPresent()) {
      LOG.debug("updating northpike_read_only role to allow password logins");

      final var passwordText =
        passwordOpt.get();
      final var settings =
        new Settings().withRenderNameCase(RenderNameCase.LOWER);
      final var dslContext =
        DSL.using(connection, POSTGRES, settings);

      dslContext.execute(
        "ALTER ROLE northpike_read_only WITH PASSWORD {0}",
        DSL.inline(passwordText)
      );

      try (var st = connection.createStatement()) {
        st.execute("ALTER ROLE northpike_read_only LOGIN");
      }
    } else {
      LOG.debug("updating northpike_read_only role to disallow logins");
      try (var st = connection.createStatement()) {
        st.execute("ALTER ROLE northpike_read_only NOLOGIN");
      }
    }
  }

  /**
   * Update the worker role password. Might be a no-op.
   */

  private static void updateWorkerRolePassword(
    final NPDatabaseConfiguration configuration,
    final Connection connection)
    throws SQLException
  {
    LOG.debug("updating northpike role");

    final var passwordText =
      configuration.workerRolePassword();
    final var settings =
      new Settings().withRenderNameCase(RenderNameCase.LOWER);
    final var dslContext =
      DSL.using(connection, POSTGRES, settings);
    dslContext.execute(
      "ALTER ROLE northpike WITH PASSWORD {0}",
      DSL.inline(passwordText)
    );

    try (var st = connection.createStatement()) {
      st.execute("ALTER ROLE northpike LOGIN");
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
    if (event instanceof final TrEventExecutingSQL sql) {
      publishEvent(
        startupMessages,
        String.format("Executing SQL: %s", sql.statement())
      );
      return;
    }

    if (event instanceof final TrEventUpgrading upgrading) {
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
