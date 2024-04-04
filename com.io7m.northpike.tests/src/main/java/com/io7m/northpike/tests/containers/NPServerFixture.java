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
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesAssign;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.NPServers;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerArchiveConfiguration;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.server.api.NPServerMaintenanceConfiguration;
import com.io7m.northpike.server.api.NPServerType;
import com.io7m.northpike.server.api.NPServerUserConfiguration;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.NPUserClients;
import com.io7m.northpike.user_client.api.NPUserClientConfiguration;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.URI;
import java.nio.file.Path;
import java.time.Clock;
import java.time.Duration;
import java.util.Locale;
import java.util.Objects;
import java.util.UUID;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.io7m.northpike.model.tls.NPTLSDisabled.TLS_DISABLED;
import static com.io7m.northpike.tests.containers.NPIdstoreFixture.PASSWORD;
import static java.util.Optional.empty;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

public final class NPServerFixture
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPServerFixture.class);

  static final NPServers SERVERS =
    new NPServers();

  private static final NPUserClients USER_CLIENTS =
    new NPUserClients();

  private static final NPStrings STRINGS =
    NPStrings.create(Locale.ROOT);

  private final NPIdstoreFixture idstoreFixture;
  private final NPDatabaseFixture databaseFixture;
  private final NPServerType server;
  private final String address;
  private final int userApiPort;

  private NPServerFixture(
    final NPIdstoreFixture inIdstoreFixture,
    final NPDatabaseFixture inDatabaseFixture,
    final NPServerType inServer,
    final String inAddress,
    final int inUserApiPort)
  {
    this.idstoreFixture =
      Objects.requireNonNull(inIdstoreFixture, "idstoreFixture");
    this.databaseFixture =
      Objects.requireNonNull(inDatabaseFixture, "databaseFixture");
    this.server =
      Objects.requireNonNull(inServer, "server");
    this.address =
      Objects.requireNonNull(inAddress, "address");
    this.userApiPort =
      inUserApiPort;
  }

  public static NPServerFixture create(
    final NPIdstoreFixture idstoreFixture,
    final NPDatabaseFixture databaseFixture,
    final Path baseDirectory,
    final int agentApiPort,
    final int userApiPort,
    final int archivePort)
    throws Exception
  {
    final var userAPIURI =
      "http://%s:%d/".formatted(
        "[::]",
        Integer.valueOf(idstoreFixture.userAPIPort())
      );

    final var userViewURI =
      "http://%s:%d/".formatted(
        "[::]",
        Integer.valueOf(idstoreFixture.userViewPort())
      );

    final var configuration =
      new NPServerConfiguration(
        Locale.ROOT,
        Clock.systemUTC(),
        NPStrings.create(Locale.ROOT),
        NPDatabaseFixture.DATABASES,
        databaseFixture.configuration(),
        new NPServerDirectoryConfiguration(
          baseDirectory.resolve("repositories"),
          baseDirectory.resolve("archives")
        ),
        new NPServerIdstoreConfiguration(
          URI.create(userAPIURI),
          URI.create(userViewURI)
        ),
        new NPServerAgentConfiguration(
          InetAddress.getByName("[::]"),
          agentApiPort,
          TLS_DISABLED,
          1_000_000
        ),
        new NPServerArchiveConfiguration(
          InetAddress.getByName("[::]"),
          archivePort,
          TLS_DISABLED,
          URI.create("https://archives.example.com/")
        ),
        new NPServerUserConfiguration(
          InetAddress.getByName("[::]"),
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
        idstoreFixture,
        databaseFixture,
        SERVERS.createServer(configuration),
        "[::]",
        userApiPort
      );

    fixture.server.start();
    fixture.reset();
    return fixture;
  }

  private static void setupUser(
    final String address,
    final int port,
    final IdUser admin,
    final IdUser user,
    final NPSecRole... roles)
    throws Exception
  {
    final var configuration =
      new NPUserClientConfiguration(STRINGS, 1_000_000);

    final var roleSet =
      Stream.of(roles)
      .map(NPSecRole::role)
      .collect(Collectors.toSet());

    try (var userClient = USER_CLIENTS.createUserClient(configuration)) {
      LOG.info(
        "Setup user: Logging in as {} ({})", admin.idName(), admin.id());
      userClient.login(
        new InetSocketAddress(address, port),
        TLS_DISABLED,
        admin.idName(),
        PASSWORD
      );

      LOG.info(
        "Setup user: Setting up {} ({}) {}", user.idName(), user.id(), roleSet);
      final var r =
        userClient.execute(
          new NPUCommandUserRolesAssign(UUID.randomUUID(), user.id(), roleSet)
        );

      assertInstanceOf(NPUResponseOK.class, r);
      LOG.info(
        "Setup user: Finished setting up {} ({})", user.idName(), user.id());
    }
  }

  private static void login(
    final String address,
    final int port,
    final IdUser user)
    throws Exception
  {
    final var configuration =
      new NPUserClientConfiguration(STRINGS, 1_000_000);

    try (var userClient = USER_CLIENTS.createUserClient(configuration)) {
      LOG.info("Login: Logging in as {} ({})", user.idName(), user.id());
      userClient.login(
        new InetSocketAddress(address, port),
        TLS_DISABLED,
        user.idName(),
        PASSWORD
      );
    }
  }

  public NPServerType server()
  {
    return this.server;
  }

  public NPDatabaseConnectionType databaseConnection()
    throws Exception
  {
    return this.server.database().openConnection(NPDatabaseRole.NORTHPIKE);
  }

  public void reset()
    throws Exception
  {
    this.server.close();
    this.databaseFixture.reset();
    this.server.start();

    this.server.setUserAsAdmin(
      this.idstoreFixture.userWithAdminId(),
      this.idstoreFixture.userWithAdminName()
    );

    setupUser(
      this.address,
      this.userApiPort,
      this.idstoreFixture.userWithAdmin(),
      this.idstoreFixture.userWithAdmin(),
      NPSecRole.ADMINISTRATOR
    );
    setupUser(
      this.address,
      this.userApiPort,
      this.idstoreFixture.userWithAdmin(),
      this.idstoreFixture.userWithLogin(),
      NPSecRole.LOGIN
    );
    setupUser(
      this.address,
      this.userApiPort,
      this.idstoreFixture.userWithAdmin(),
      this.idstoreFixture.userWithoutLogin()
    );

    login(this.address, this.userApiPort, this.idstoreFixture.userWithLogin());
  }

  public void start()
    throws Exception
  {
    this.server.start();
  }

  public void stop()
    throws Exception
  {
    this.server.close();
  }

  public NPIdstoreFixture idstore()
  {
    return this.idstoreFixture;
  }
}
