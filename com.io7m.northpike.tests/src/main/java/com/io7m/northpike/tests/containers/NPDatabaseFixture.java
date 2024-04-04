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


package com.io7m.northpike.tests.containers;

import com.io7m.idstore.model.IdUser;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.api.NPDatabaseCreate;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTelemetry;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUpgrade;
import com.io7m.northpike.database.postgres.NPPGDatabases;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import org.junit.jupiter.api.Assertions;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Clock;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * A northpike database fixture.
 */

public final class NPDatabaseFixture
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDatabaseFixture.class);

  static final NPPGDatabases DATABASES =
    new NPPGDatabases();

  private final NPPostgresFixture postgres;
  private final NPDatabaseConfiguration configuration;

  private NPDatabaseFixture(
    final NPPostgresFixture inPostgres,
    final NPDatabaseConfiguration inConfiguration)
  {
    this.postgres =
      Objects.requireNonNull(inPostgres, "postgres");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
  }

  public static NPDatabaseFixture create(
    final NPPostgresFixture postgres)
    throws Exception
  {
    final var configuration =
      new NPDatabaseConfiguration(
        postgres.databaseOwner(),
        "12345678",
        "12345678",
        Optional.of("12345678"),
        "::",
        postgres.port(),
        "northpike",
        NPDatabaseCreate.CREATE_DATABASE,
        NPDatabaseUpgrade.UPGRADE_DATABASE,
        false,
        "english",
        Clock.systemUTC(),
        NPStrings.create(Locale.ROOT)
      );

    final var r =
      postgres.container()
        .executeAndWait(
          List.of(
            "createdb",
            "-w",
            "-U",
            postgres.databaseOwner(),
            "northpike"
          ),
          10L,
          TimeUnit.SECONDS
        );

    Assertions.assertEquals(0, r);

    return new NPDatabaseFixture(
      postgres,
      configuration
    );
  }

  public NPDatabaseConfiguration configuration()
  {
    return this.configuration;
  }

  public void reset()
    throws Exception
  {
    {
      final var r =
        this.postgres.container()
          .executeAndWait(
            List.of(
              "dropdb",
              "-f",
              "-w",
              "-U",
              this.postgres.databaseOwner(),
              "northpike"
            ),
            10L,
            TimeUnit.SECONDS
          );
      Assertions.assertEquals(0, r);
    }

    {
      final var r =
        this.postgres.container()
          .executeAndWait(
            List.of(
              "createdb",
              "-w",
              "-U",
              this.postgres.databaseOwner(),
              "northpike"
            ),
            10L,
            TimeUnit.SECONDS
          );
      Assertions.assertEquals(0, r);
    }
  }

  public NPDatabaseType createDatabase()
    throws Exception
  {
    return DATABASES.open(
      this.configuration,
      new NPDatabaseTelemetry(
        true,
        NPTelemetryNoOp.noop().meter(),
        NPTelemetryNoOp.noop().tracer()
      ),
      message -> LOG.info("Database setup: {}", message)
    );
  }

  public NPAuditOwnerType.User userSetup(
    final IdUser user)
    throws Exception
  {
    try (var database = this.createDatabase()) {
      try (var connection = database.openConnection(NPDatabaseRole.NORTHPIKE)) {
        try (var transaction = connection.openTransaction()) {
          transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
            .execute(new NPUser(
              user.id(),
              user.idName(),
              new MSubject(Set.of())
            ));
          transaction.commit();
          return new NPAuditOwnerType.User(user.id());
        }
      }
    }
  }
}
