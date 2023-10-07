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


package com.io7m.northpike.tests.containers;


import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.api.EContainerType;
import com.io7m.ervilla.postgres.EPgSpecs;
import com.io7m.idstore.model.IdName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseCreate;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTelemetry;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUpgrade;
import com.io7m.northpike.database.postgres.NPPGDatabases;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.server.NPServers;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerArchiveConfiguration;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.api.NPServerFactoryType;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.server.api.NPServerMaintenanceConfiguration;
import com.io7m.northpike.server.api.NPServerType;
import com.io7m.northpike.server.api.NPServerUserConfiguration;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.NPTestProperties;
import io.opentelemetry.api.OpenTelemetry;
import org.junit.jupiter.api.Assertions;

import java.io.IOException;
import java.net.InetAddress;
import java.net.URI;
import java.nio.file.Path;
import java.time.Clock;
import java.time.Duration;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.tls.NPTLSDisabled.TLS_DISABLED;
import static java.util.Optional.empty;

public final class NPTestContainers
{
  private static final NPPGDatabases DATABASES =
    new NPPGDatabases();
  private static final NPServerFactoryType SERVERS =
    new NPServers();

  private NPTestContainers()
  {

  }

  /**
   * The basic database fixture.
   *
   * @param configuration The database configuration
   * @param container     The database container
   */

  public record NPDatabaseFixture(
    EContainerType container,
    NPDatabaseConfiguration configuration)
  {
    /**
     * Create a database from this container and configuration.
     *
     * @return A new database
     *
     * @throws NPDatabaseException On errors
     */

    public NPDatabaseType createDatabase()
      throws NPDatabaseException
    {
      return DATABASES.open(
        this.configuration,
        new NPDatabaseTelemetry(
          true,
          OpenTelemetry.noop().getMeter("x"),
          OpenTelemetry.noop().getTracer("x")
        ),
        message -> {

        });
    }

    /**
     * Reset the container by dropping and recreating the database. This
     * is significantly faster than destroying and recreating the container.
     *
     * @throws IOException          On errors
     * @throws InterruptedException On interruption
     */

    public void reset()
      throws IOException, InterruptedException
    {
      Assertions.assertEquals(
        0,
        this.container.executeAndWaitIndefinitely(
          List.of(
            "dropdb",
            "-w",
            "-f",
            "-U",
            "northpike_install",
            "northpike"
          )
        ));

      Assertions.assertEquals(
        0,
        this.container.executeAndWaitIndefinitely(
          List.of(
            "createdb",
            "-w",
            "-U",
            "northpike_install",
            "northpike"
          )
        )
      );
    }

    public static NPAuditUserOrAgentType.User createUser(
      final NPDatabaseTransactionType transaction,
      final UUID userId)
      throws NPDatabaseException
    {
      transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
        .execute(new NPUser(
          userId,
          new IdName("example"),
          new MSubject(Set.of())
        ));
      transaction.commit();
      return new NPAuditUserOrAgentType.User(userId);
    }
  }

  public static NPDatabaseFixture createDatabase(
    final EContainerSupervisorType supervisor,
    final int port)
    throws IOException, InterruptedException
  {
    final var container =
      supervisor.start(
        EPgSpecs.builderFromDockerIO(
          NPTestProperties.POSTGRESQL_VERSION,
          Optional.empty(),
          port,
          "northpike",
          "northpike_install",
          "12345678"
        ).build()
      );

    final var configuration =
      new NPDatabaseConfiguration(
        "northpike_install",
        "12345678",
        "12345678",
        Optional.of("12345678"),
        "localhost",
        port,
        "northpike",
        NPDatabaseCreate.CREATE_DATABASE,
        NPDatabaseUpgrade.UPGRADE_DATABASE,
        false,
        "english",
        Clock.systemUTC(),
        NPStrings.create(Locale.ROOT)
      );

    return new NPDatabaseFixture(
      container,
      configuration
    );
  }

  public static NPDatabaseFixture createDatabaseWithHostilePasswords(
    final EContainerSupervisorType supervisor,
    final int port)
    throws IOException, InterruptedException
  {
    final var ownerRolePassword = "''\\'1";
    final var workerRolePassword = "''\\'2";
    final var readerRolePassword = "''\\'3";

    final var container =
      supervisor.start(
        EPgSpecs.builderFromDockerIO(
          NPTestProperties.POSTGRESQL_VERSION,
          Optional.empty(),
          port,
          "northpike",
          "northpike_install",
          ownerRolePassword
        ).build()
      );

    final var configuration =
      new NPDatabaseConfiguration(
        "northpike_install",
        ownerRolePassword,
        workerRolePassword,
        Optional.of(readerRolePassword),
        "localhost",
        port,
        "northpike",
        NPDatabaseCreate.CREATE_DATABASE,
        NPDatabaseUpgrade.UPGRADE_DATABASE,
        false,
        "english",
        Clock.systemUTC(),
        NPStrings.create(Locale.ROOT)
      );

    return new NPDatabaseFixture(
      container,
      configuration
    );
  }

  public record NPServerFixture(
  NPDatabaseFixture databaseFixture,
  NPServerType server)
  implements AutoCloseable
{
  @Override
  public void close()
    throws Exception
  {
    this.server.close();
  }

  public void setUserAsAdmin(
    final UUID userId,
    final String userName)
    throws NPServerException
  {
    this.server.setUserAsAdmin(userId, new IdName(userName));
  }

  public void reset()
    throws Exception
  {
    this.databaseFixture.reset();
    this.server.close();
  }

  public void start()
    throws Exception
  {
    this.server.start();
  }

  public NPDatabaseConnectionType databaseConnection()
    throws NPDatabaseException
  {
    return this.server.database()
      .openConnection(NPDatabaseRole.NORTHPIKE);
  }

}

  public static NPServerFixture createServer(
    final NPIdstoreFixture idstoreFixture,
    final NPDatabaseFixture databaseFixture,
    final Path baseDirectory,
    final int agentApiPort,
    final int userApiPort,
    final int archivePort)
    throws IOException, NPServerException
  {
    final NPServerConfiguration configuration =
      new NPServerConfiguration(
        Locale.ROOT,
        Clock.systemUTC(),
        NPStrings.create(Locale.ROOT),
        DATABASES,
        databaseFixture.configuration,
        new NPServerDirectoryConfiguration(
          baseDirectory.resolve("repositories"),
          baseDirectory.resolve("archives")),
        new NPServerIdstoreConfiguration(
          URI.create("http://localhost:" + idstoreFixture.userAPIPort()),
          URI.create("http://localhost:" + idstoreFixture.userAPIPort())
        ),
        new NPServerAgentConfiguration(
          InetAddress.getLocalHost(),
          agentApiPort,
          TLS_DISABLED,
          1_000_000
        ),
        new NPServerArchiveConfiguration(
          InetAddress.getLocalHost(),
          archivePort,
          TLS_DISABLED,
          URI.create("https://archives.example.com/")
        ),
        new NPServerUserConfiguration(
          InetAddress.getLocalHost(),
          userApiPort,
          TLS_DISABLED,
          1_000_000
        ),
        new NPServerMaintenanceConfiguration(
          empty(),
          Duration.ofDays(1L),
          Duration.ofDays(1L),
          Duration.ofDays(1L)
        ),
        empty()
      );

    final var fixture =
      new NPServerFixture(
        databaseFixture,
        SERVERS.createServer(configuration)
      );

    fixture.server.start();
    return fixture;
  }
}
