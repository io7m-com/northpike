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


package com.io7m.northpike.tests.agent.database;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseConfiguration;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseCreate;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUpgrade;
import com.io7m.northpike.agent.database.sqlite.NPASDatabases;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.sqlite.SQLiteConfig;
import org.sqlite.SQLiteDataSource;

import java.nio.file.Path;
import java.time.Clock;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPAgentDatabaseSetupTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentDatabaseSetupTest.class);

  @Test
  public void testWrongDatabaseApplicationID(
    final @TempDir Path directory)
    throws Exception
  {
    final var otherDb =
      directory.resolve("agent.db");

    {
      final var url = new StringBuilder(128);
      url.append("jdbc:sqlite:");
      url.append(otherDb.toAbsolutePath());

      final var config = new SQLiteConfig();
      config.setApplicationId(0x50494b45);
      config.enforceForeignKeys(true);

      final var dataSource = new SQLiteDataSource(config);
      dataSource.setUrl(url.toString());

      final var table = """
        CREATE TABLE schema_version (
          version_lock            INTEGER NOT NULL DEFAULT 1,
          version_application_id  TEXT    NOT NULL,
          version_number          INTEGER NOT NULL,

          CONSTRAINT check_lock_primary
            PRIMARY KEY (version_lock),

          CONSTRAINT check_lock_locked
            CHECK (version_lock = 1)
        )
        STRICT
              """;

      final var insert = """
        insert into schema_version (version_application_id, version_number) values (?, ?)
                      """;

      try (var conn = dataSource.getConnection()) {
        conn.setAutoCommit(false);

        try (var st = conn.prepareStatement(table)) {
          st.execute();
        }
        try (var st = conn.prepareStatement(insert)) {
          st.setString(1, "com.io7m.northpike.other");
          st.setLong(2, 0L);
          st.execute();
        }
        conn.commit();
      }
    }

    final var databases =
      new NPASDatabases();

    final var ex =
      assertThrows(NPAgentDatabaseException.class, () -> {
        databases.open(
          new NPAgentDatabaseSetup(
            new NPAgentDatabaseConfiguration(
              "SQLITE",
              otherDb,
              NPAgentDatabaseCreate.CREATE_DATABASE,
              NPAgentDatabaseUpgrade.UPGRADE_DATABASE
            ),
            NPTelemetryNoOp.noop(),
            Clock.systemUTC(),
            NPStrings.create(Locale.getDefault())
          ),
          s -> LOG.debug("{}", s)
        );
      });
    assertTrue(ex.getMessage().contains("com.io7m.northpike.other"));
  }

  @Test
  public void testNoSchemaVersion(
    final @TempDir Path directory)
    throws Exception
  {
    final var otherDb =
      directory.resolve("agent.db");

    {
      final var url = new StringBuilder(128);
      url.append("jdbc:sqlite:");
      url.append(otherDb.toAbsolutePath());

      final var config = new SQLiteConfig();
      config.setApplicationId(0x50494b45);
      config.enforceForeignKeys(true);

      final var dataSource = new SQLiteDataSource(config);
      dataSource.setUrl(url.toString());

      final var table = """
        CREATE TABLE schema_version (
          version_lock            INTEGER NOT NULL DEFAULT 1,
          version_application_id  TEXT    NOT NULL,
          version_number          INTEGER NOT NULL,

          CONSTRAINT check_lock_primary
            PRIMARY KEY (version_lock),

          CONSTRAINT check_lock_locked
            CHECK (version_lock = 1)
        )
        STRICT
              """;

      try (var conn = dataSource.getConnection()) {
        conn.setAutoCommit(false);
        try (var st = conn.prepareStatement(table)) {
          st.execute();
        }
        conn.commit();
      }
    }

    final var databases =
      new NPASDatabases();

    final var ex =
      assertThrows(NPAgentDatabaseException.class, () -> {
        databases.open(
          new NPAgentDatabaseSetup(
            new NPAgentDatabaseConfiguration(
              "SQLITE",
              otherDb,
              NPAgentDatabaseCreate.CREATE_DATABASE,
              NPAgentDatabaseUpgrade.UPGRADE_DATABASE
            ),
            NPTelemetryNoOp.noop(),
            Clock.systemUTC(),
            NPStrings.create(Locale.getDefault())
          ),
          s -> LOG.debug("{}", s)
        );
      });
    assertEquals(ex.getMessage(), "schema_version table is empty!");
  }

  @Test
  public void testUnknownSchemaVersion(
    final @TempDir Path directory)
    throws Exception
  {
    final var otherDb =
      directory.resolve("agent.db");

    {
      final var url = new StringBuilder(128);
      url.append("jdbc:sqlite:");
      url.append(otherDb.toAbsolutePath());

      final var config = new SQLiteConfig();
      config.setApplicationId(0x50494b45);
      config.enforceForeignKeys(true);

      final var dataSource = new SQLiteDataSource(config);
      dataSource.setUrl(url.toString());

      final var table = """
        CREATE TABLE schema_version (
          version_lock            INTEGER NOT NULL DEFAULT 1,
          version_application_id  TEXT    NOT NULL,
          version_number          INTEGER NOT NULL,

          CONSTRAINT check_lock_primary
            PRIMARY KEY (version_lock),

          CONSTRAINT check_lock_locked
            CHECK (version_lock = 1)
        )
        STRICT
              """;

      final var insert = """
        insert into schema_version (version_application_id, version_number) values (?, ?)
                      """;

      try (var conn = dataSource.getConnection()) {
        conn.setAutoCommit(false);
        try (var st = conn.prepareStatement(table)) {
          st.execute();
        }
        try (var st = conn.prepareStatement(insert)) {
          st.setString(1, "com.io7m.northpike");
          st.setLong(2, 1000L);
          st.execute();
        }
        conn.commit();
      }
    }

    final var databases =
      new NPASDatabases();

    final var ex =
      assertThrows(NPAgentDatabaseException.class, () -> {
        databases.open(
          new NPAgentDatabaseSetup(
            new NPAgentDatabaseConfiguration(
              "SQLITE",
              otherDb,
              NPAgentDatabaseCreate.CREATE_DATABASE,
              NPAgentDatabaseUpgrade.UPGRADE_DATABASE
            ),
            NPTelemetryNoOp.noop(),
            Clock.systemUTC(),
            NPStrings.create(Locale.getDefault())
          ),
          s -> LOG.debug("{}", s)
        );
      });
    assertEquals(ex.getMessage(), "Database schema version is too high!");
  }
}
