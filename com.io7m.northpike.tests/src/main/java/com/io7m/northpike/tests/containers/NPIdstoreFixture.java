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
import com.io7m.northpike.tests.NPTestProperties;
import org.junit.jupiter.api.Assertions;

import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.ervilla.api.EPortProtocol.TCP;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.util.Optional.empty;

public final class NPIdstoreFixture
{
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

  private static final IdName USER_WITH_LOGIN_NAME =
    new IdName("user-with-login");
  private static final IdName USER_WITHOUT_LOGIN_NAME =
    new IdName("user-without-login");
  private static final String PASSWORD =
    "12345678";

  private final EContainerType serverContainer;
  private final EContainerType databaseContainer;
  private final UUID adminId;
  private final String adminName;
  private final String adminPassword;
  private final int adminAPIPort;
  private final int userAPIPort;
  private UUID userWithLogin;
  private UUID userWithoutLogin;

  public NPIdstoreFixture(
    final EContainerType inServerContainer,
    final EContainerType inDatabaseContainer,
    final UUID inAdminId,
    final String inAdminName,
    final String inAdminPassword,
    final int inAdminAPIPort,
    final int inUserAPIPort)
  {
    this.serverContainer =
      Objects.requireNonNull(inServerContainer, "serverContainer");
    this.databaseContainer =
      Objects.requireNonNull(inDatabaseContainer, "databaseContainer");
    this.adminId =
      Objects.requireNonNull(inAdminId, "adminId");
    this.adminName =
      Objects.requireNonNull(inAdminName, "adminName");
    this.adminPassword =
      Objects.requireNonNull(inAdminPassword, "adminPassword");
    this.adminAPIPort =
      inAdminAPIPort;
    this.userAPIPort =
      inUserAPIPort;
  }

  public static NPIdstoreFixture createIdstore(
    final EContainerSupervisorType supervisor,
    final Path configurationDirectory,
    final int databasePort,
    final int adminAPIPort,
    final int userAPIPort,
    final int userViewPort)
    throws Exception
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
    fixture.userWithLogin =
      fixture.createUser(USER_WITH_LOGIN_NAME);
    fixture.userWithoutLogin =
      fixture.createUser(USER_WITHOUT_LOGIN_NAME);

    return fixture;
  }

  public IdName userWithLoginName()
  {
    return USER_WITH_LOGIN_NAME;
  }

  public IdName userWithoutLoginName()
  {
    return USER_WITHOUT_LOGIN_NAME;
  }

  public UUID userWithLogin()
  {
    return this.userWithLogin;
  }

  public UUID userWithoutLogin()
  {
    return this.userWithoutLogin;
  }

  public EContainerType serverContainer()
  {
    return this.serverContainer;
  }

  public EContainerType databaseContainer()
  {
    return this.databaseContainer;
  }

  public UUID adminId()
  {
    return this.adminId;
  }

  public String adminName()
  {
    return this.adminName;
  }

  public String adminPassword()
  {
    return this.adminPassword;
  }

  public int adminAPIPort()
  {
    return this.adminAPIPort;
  }

  public int userAPIPort()
  {
    return this.userAPIPort;
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

  private UUID createUser(
    final IdName userName)
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
            userName,
            new IdRealName(userName.value()),
            new IdEmail("%s@example.com".formatted(userName)),
            IdPasswordAlgorithmPBKDF2HmacSHA256.create()
              .createHashed(PASSWORD)
          ),
          IdAClientException::ofError
        );

      return response.user().id();
    }
  }

  public String password()
  {
    return PASSWORD;
  }
}
