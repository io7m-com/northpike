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


import com.io7m.ervilla.api.EContainerSpec;
import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.api.EContainerType;
import com.io7m.ervilla.api.EPortPublish;
import com.io7m.ervilla.api.EVolumeMount;
import com.io7m.ervilla.postgres.EPgSpecs;
import com.io7m.idstore.admin_client.IdAClients;
import com.io7m.idstore.admin_client.api.IdAClientConfiguration;
import com.io7m.idstore.admin_client.api.IdAClientCredentials;
import com.io7m.idstore.admin_client.api.IdAClientException;
import com.io7m.idstore.model.IdEmail;
import com.io7m.idstore.model.IdName;
import com.io7m.idstore.model.IdPasswordAlgorithmPBKDF2HmacSHA256;
import com.io7m.idstore.model.IdRealName;
import com.io7m.idstore.protocol.admin.IdACommandUserCreate;
import com.io7m.idstore.protocol.admin.IdAResponseUserCreate;
import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseCreate;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTelemetry;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUpgrade;
import com.io7m.northpike.database.postgres.NPPGDatabases;
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
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Clock;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.ervilla.api.EPortProtocol.TCP;
import static com.io7m.northpike.tls.NPTLSDisabled.TLS_DISABLED;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
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

  public record NPIdstoreFixture(
    EContainerType serverContainer,
    EContainerType databaseContainer,
    UUID adminId,
    String adminName,
    String adminPassword,
    int adminAPIPort, int userAPIPort)
  {
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
      this.serverContainer.stop();

      Assertions.assertEquals(
        0,
        this.databaseContainer.executeAndWaitIndefinitely(
          List.of(
            "dropdb",
            "-w",
            "-f",
            "-U",
            "idstore_install",
            "idstore"
          )
        )
      );

      Assertions.assertEquals(
        0,
        this.databaseContainer.executeAndWaitIndefinitely(
          List.of(
            "createdb",
            "-w",
            "-U",
            "idstore_install",
            "idstore"
          )
        )
      );

      this.serverContainer.start();
      this.initialAdmin();
    }

    private void initialAdmin()
      throws IOException, InterruptedException
    {
      for (int index = 0; index < 5; ++index) {
        final var r = this.serverContainer.executeAndWaitIndefinitely(
          List.of(
            "idstore",
            "initial-admin",
            "--configuration",
            "/idstore/etc/server.xml",
            "--admin-id",
            this.adminId.toString(),
            "--admin-username",
            "admin",
            "--admin-password",
            "12345678",
            "--admin-email",
            "admin@example.com",
            "--admin-realname",
            "admin"
          )
        );
        if (r == 0) {
          return;
        }
        Thread.sleep(250L);
      }

      throw new IllegalStateException(
        "Failed to create initial admin after several attempts."
      );
    }

    public UUID createUser(
      final String userName)
      throws Exception
    {
      final var clients = new IdAClients();
      try (var client =
             clients.openSynchronousClient(
               new IdAClientConfiguration(Locale.ROOT))) {

        client.loginOrElseThrow(
          new IdAClientCredentials(
            this.adminName,
            this.adminPassword,
            URI.create(
              "http://localhost:%d".formatted(Integer.valueOf(this.adminAPIPort))
            ),
            Map.of()
          ),
          IdAClientException::ofError
        );

        final IdAResponseUserCreate response =
          (IdAResponseUserCreate) client.executeOrElseThrow(
            new IdACommandUserCreate(
              empty(),
              new IdName(userName),
              new IdRealName(userName),
              new IdEmail("%s@example.com".formatted(userName)),
              IdPasswordAlgorithmPBKDF2HmacSHA256.create()
                .createHashed("12345678")
            ),
            IdAClientException::ofError
          );

        return response.user().id();
      }
    }
  }

  public static NPIdstoreFixture createIdstore(
    final EContainerSupervisorType supervisor,
    final Path configurationDirectory,
    final int databasePort,
    final int adminAPIPort,
    final int userAPIPort,
    final int userViewPort)
    throws IOException, InterruptedException
  {
    final var pod =
      supervisor.createPod(List.of(
        new EPortPublish(empty(), databasePort, 5432, TCP),
        new EPortPublish(empty(), adminAPIPort, 51000, TCP),
        new EPortPublish(empty(), userAPIPort, 50000, TCP),
        new EPortPublish(empty(), userViewPort, 50001, TCP)
      ));

    final var databaseContainer =
      pod.start(
        EPgSpecs.builderFromDockerIO(
          NPTestProperties.POSTGRESQL_VERSION,
          Optional.empty(),
          databasePort,
          "idstore",
          "idstore_install",
          "12345678"
        ).build()
      );

    Files.writeString(
      configurationDirectory.resolve("server.xml"),
      IDSTORE_CONFIGURATION_TEMPLATE.trim(),
      StandardCharsets.UTF_8,
      CREATE,
      TRUNCATE_EXISTING
    );

    final var serverContainer =
      pod.start(
        EContainerSpec.builder(
            "quay.io",
            "io7mcom/idstore",
            NPTestProperties.IDSTORE_VERSION)
          .addVolumeMount(
            new EVolumeMount(
              configurationDirectory, "/idstore/etc")
          )
          .addArgument("server")
          .addArgument("--verbose")
          .addArgument("debug")
          .addArgument("--configuration")
          .addArgument("/idstore/etc/server.xml")
          .setReadyCheck(new NPIdstoreHealthcheck("localhost", adminAPIPort))
          .build()
      );

    final var fixture =
      new NPIdstoreFixture(
        serverContainer,
        databaseContainer,
        UUID.randomUUID(),
        "admin",
        "12345678",
        adminAPIPort,
        userAPIPort
      );

    fixture.initialAdmin();
    return fixture;
  }

  private static final String IDSTORE_CONFIGURATION_TEMPLATE = """
    <?xml version="1.0" encoding="UTF-8" ?>
    <Configuration xmlns="urn:com.io7m.idstore:configuration:1">
      <Branding ProductTitle="idstore"/>
      <Database Name="idstore"
                Kind="POSTGRESQL"
                OwnerRoleName="idstore_install"
                OwnerRolePassword="12345678"
                WorkerRolePassword="12345678"
                Address="localhost"
                Port="5432"
                Create="true"
                Upgrade="true"/>
      <HTTPServices>
        <HTTPServiceAdminAPI ListenAddress="[::]" ListenPort="51000" ExternalURI="http://[::]:51000/"/>
        <HTTPServiceUserAPI ListenAddress="[::]" ListenPort="50000" ExternalURI="http://[::]:50000/"/>
        <HTTPServiceUserView ListenAddress="[::]" ListenPort="50001" ExternalURI="http://[::]:50001/"/>
      </HTTPServices>
      <History UserLoginHistoryLimit="10" AdminLoginHistoryLimit="100"/>
      <Mail SenderAddress="northpike@example.com" VerificationExpiration="PT24H">
        <SMTP Host="localhost" Port="25"/>
      </Mail>
      <RateLimiting EmailVerificationRateLimit="PT1M"
                    UserLoginRateLimit="PT0S"
                    AdminLoginRateLimit="PT0S"
                    PasswordResetRateLimit="PT1M"/>
      <Sessions UserSessionExpiration="PT60M"
                AdminSessionExpiration="PT60M"/>
    </Configuration>
    """;

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
          URI.create("http://localhost:" + idstoreFixture.userAPIPort),
          URI.create("http://localhost:" + idstoreFixture.userAPIPort)
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
          Optional.empty()
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
