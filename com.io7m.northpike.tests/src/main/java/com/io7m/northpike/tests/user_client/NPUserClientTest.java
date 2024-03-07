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


package com.io7m.northpike.tests.user_client;

import com.io7m.ervilla.api.EContainerSupervisorType;
import com.io7m.ervilla.test_extension.ErvillaCloseAfterSuite;
import com.io7m.ervilla.test_extension.ErvillaConfiguration;
import com.io7m.ervilla.test_extension.ErvillaExtension;
import com.io7m.idstore.model.IdName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySearchParameters;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.protocol.user.NPUCommandAgentsConnected;
import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryGet;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionPut;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUCommandUsersConnected;
import com.io7m.northpike.protocol.user.cb.NPU1Messages;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPFixtures;
import com.io7m.northpike.tests.containers.NPIdstoreFixture;
import com.io7m.northpike.tests.containers.NPServerFixture;
import com.io7m.northpike.user_client.NPUserClients;
import com.io7m.northpike.user_client.api.NPUserClientConfiguration;
import com.io7m.northpike.user_client.api.NPUserClientException;
import com.io7m.northpike.user_client.api.NPUserClientType;
import com.io7m.zelador.test_extension.ZeladorExtension;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.extension.ExtendWith;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ServerSocketFactory;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.net.URI;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.stream.Collectors;

import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.ALLOW_UNSIGNED_COMMITS;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.security.NPSecRole.AGENTS_READER;
import static com.io7m.northpike.model.security.NPSecRole.LOGIN;
import static com.io7m.northpike.model.security.NPSecRole.REPOSITORIES_READER;
import static com.io7m.northpike.model.security.NPSecRole.REPOSITORIES_WRITER;
import static com.io7m.northpike.model.security.NPSecRole.TOOLS_READER;
import static com.io7m.northpike.model.security.NPSecRole.TOOLS_WRITER;
import static com.io7m.northpike.model.security.NPSecRole.USERS_READER;
import static com.io7m.northpike.model.tls.NPTLSDisabled.TLS_DISABLED;
import static java.net.StandardSocketOptions.SO_REUSEADDR;
import static java.net.StandardSocketOptions.SO_REUSEPORT;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

@Timeout(30L)
@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPUserClientTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPUserClientTest.class);

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private static NPIdstoreFixture IDSTORE_FIXTURE;
  private static NPServerFixture SERVER_FIXTURE;

  private ServerSocket socket;
  private NPStrings strings;
  private ExecutorService executor;
  private CountDownLatch serverAcceptLatch;
  private NPUserClientConfiguration configuration;
  private NPUserClients users;
  private NPUserClientType userClient;
  private InetSocketAddress serverAddress;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    SERVER_FIXTURE =
      NPFixtures.server(containers);
    IDSTORE_FIXTURE =
      SERVER_FIXTURE.idstore();
  }

  @BeforeEach
  public void setup()
    throws Exception
  {
    SERVER_FIXTURE.reset();
    SERVER_FIXTURE.start();

    this.executor =
      Executors.newSingleThreadExecutor();
    this.serverAcceptLatch =
      new CountDownLatch(1);

    this.strings =
      NPStrings.create(Locale.ROOT);

    this.socket =
      ServerSocketFactory.getDefault()
        .createServerSocket();

    this.socket.setReuseAddress(true);

    try {
      this.socket.setOption(SO_REUSEPORT, Boolean.TRUE);
    } catch (final UnsupportedOperationException e) {
      // Nothing we can do about this.
    }

    try {
      this.socket.setOption(SO_REUSEADDR, Boolean.TRUE);
    } catch (final UnsupportedOperationException e) {
      // Nothing we can do about this.
    }

    this.socket.bind(new InetSocketAddress("localhost", 0x4e50));

    this.configuration =
      new NPUserClientConfiguration(
        this.strings,
        1_000_000
      );

    this.users =
      new NPUserClients();
    this.userClient =
      this.users.createUserClient(this.configuration);

    this.serverAddress =
      new InetSocketAddress(
        SERVER_FIXTURE.server()
          .configuration()
          .userConfiguration()
          .localAddress(),
        SERVER_FIXTURE.server()
          .configuration()
          .userConfiguration()
          .localPort()
      );
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    try {
      SERVER_FIXTURE.stop();
    } catch (final Exception e) {
      LOG.error("Close: ", e);
    }

    try {
      this.userClient.close();
    } catch (final Exception e) {
      LOG.error("Close: ", e);
    }

    try {
      this.socket.close();
    } catch (final Exception e) {
      LOG.error("Close: ", e);
    }
  }

  /**
   * The connection fails if the server refuses the chosen version.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerRejectsVersion()
    throws Exception
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var inputStream =
          clientSocket.getInputStream();
        final var outputStream =
          clientSocket.getOutputStream();

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocolsAvailable(
            List.of(
              new NPIProtocol(NPU1Messages.protocolId(), 1L)
            )
          )
        );

        final var received0 =
          (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIError(
            new NPErrorCode("go-away"),
            "GO AWAY!"
          )
        );

        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPUserClientException.class, () -> {
        this.userClient.login(
          new InetSocketAddress(
            this.socket.getInetAddress(),
            this.socket.getLocalPort()
          ),
          TLS_DISABLED,
          new IdName("unused"),
          "unused"
        );
      });
    assertEquals("GO AWAY!", ex.getMessage());
  }

  /**
   * Logging in fails for nonexistent users.
   *
   * @throws Exception On errors
   */

  @Test
  public void testLoginNoSuchUser()
    throws Exception
  {
    final var ex =
      assertThrows(NPUserClientException.class, () -> {
        this.userClient.login(
          this.serverAddress,
          TLS_DISABLED,
          new IdName("nonexistent"),
          "123"
        );
      });

    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Logging in fails for users that exist but that do not have a login role.
   *
   * @throws Exception On errors
   */

  @Test
  public void testLoginNoLoginRole()
    throws Exception
  {
    final var connection =
      SERVER_FIXTURE.databaseConnection();
    final var transaction =
      connection.openTransaction();

    transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
      .execute(new NPUser(
        IDSTORE_FIXTURE.userWithoutLoginId(),
        IDSTORE_FIXTURE.userWithoutLoginName(),
        new MSubject(Set.of())
      ));

    transaction.commit();

    final var ex =
      assertThrows(NPUserClientException.class, () -> {
        this.userClient.login(
          this.serverAddress,
          TLS_DISABLED,
          IDSTORE_FIXTURE.userWithoutLoginName(),
          IDSTORE_FIXTURE.password()
        );
      });

    assertEquals(errorAuthentication(), ex.errorCode());
  }

  /**
   * Logging in succeeds for users that exist and have a login role.
   *
   * @throws Exception On errors
   */

  @Test
  public void testLoginOK()
    throws Exception
  {
    setupUser(
      IDSTORE_FIXTURE.userWithLoginId(),
      IDSTORE_FIXTURE.userWithLoginName(),
      Set.of(LOGIN)
    );

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      IDSTORE_FIXTURE.userWithLoginName(),
      IDSTORE_FIXTURE.password()
    );

    this.userClient.execute(NPUCommandDisconnect.of());
  }

  /**
   * Repositories can be read and written.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositoryReadWrite()
    throws Exception
  {
    setupUser(
      IDSTORE_FIXTURE.userWithLoginId(),
      IDSTORE_FIXTURE.userWithLoginName(),
      Set.of(LOGIN, REPOSITORIES_WRITER, REPOSITORIES_READER)
    );

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      IDSTORE_FIXTURE.userWithLoginName(),
      IDSTORE_FIXTURE.password()
    );

    final var repository =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        URI.create("http://www.example.com"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    this.userClient.execute(
      new NPUCommandRepositoryPut(randomUUID(), repository)
    );

    final var r =
      this.userClient.execute(
        new NPUCommandRepositoryGet(randomUUID(), repository.id())
      );

    assertEquals(
      Optional.of(repository),
      r.repository()
    );

    this.userClient.execute(NPUCommandDisconnect.of());
  }

  /**
   * Repositories can be searched for.
   *
   * @throws Exception On errors
   */

  @Test
  public void testRepositorySearch()
    throws Exception
  {
    setupUser(
      IDSTORE_FIXTURE.userWithLoginId(),
      IDSTORE_FIXTURE.userWithLoginName(),
      Set.of(LOGIN, REPOSITORIES_WRITER, REPOSITORIES_READER)
    );

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      IDSTORE_FIXTURE.userWithLoginName(),
      IDSTORE_FIXTURE.password()
    );

    final var repository0 =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        URI.create("http://www.example.com/0"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var repository1 =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        URI.create("http://www.example.com/1"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    final var repository2 =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(randomUUID()),
        URI.create("http://www.example.com/2"),
        CREDENTIALS_NONE,
        ALLOW_UNSIGNED_COMMITS
      );

    this.userClient.execute(
      new NPUCommandRepositoryPut(randomUUID(), repository0));
    this.userClient.execute(
      new NPUCommandRepositoryPut(randomUUID(), repository1));
    this.userClient.execute(
      new NPUCommandRepositoryPut(randomUUID(), repository2));

    final var r =
      this.userClient.execute(
        new NPUCommandRepositorySearchBegin(
          randomUUID(), new NPRepositorySearchParameters(1000L)));

    this.userClient.execute(
      new NPUCommandRepositorySearchNext(randomUUID()));
    this.userClient.execute(
      new NPUCommandRepositorySearchNext(randomUUID()));

    this.userClient.execute(
      new NPUCommandRepositorySearchPrevious(randomUUID()));
    this.userClient.execute(
      new NPUCommandRepositorySearchPrevious(randomUUID()));

    assertEquals(
      new NPPage<>(
        List.of(
          repository0.summary(),
          repository1.summary(),
          repository2.summary()
        ),
        1,
        1,
        0L
      ),
      r.results()
    );
  }

  /**
   * Tool executions can be searched for.
   *
   * @throws Exception On errors
   */

  @Test
  public void testToolExecutions()
    throws Exception
  {
    setupUser(
      IDSTORE_FIXTURE.userWithLoginId(),
      IDSTORE_FIXTURE.userWithLoginName(),
      Set.of(LOGIN, TOOLS_WRITER, TOOLS_READER)
    );

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      IDSTORE_FIXTURE.userWithLoginName(),
      IDSTORE_FIXTURE.password()
    );

    final var identifier =
      new NPToolExecutionIdentifier(
        NPToolExecutionName.of("com.io7m.ex0"),
        1L
      );

    final var description =
      new NPToolExecutionDescription(
        identifier,
        NPToolName.of("org.apache.maven"),
        "An execution.",
        NPFormatName.of("com.io7m.northpike.toolexec.js"),
        "execution.argumentAdd('ok')"
      );

    this.userClient.execute(
      new NPUCommandToolExecutionDescriptionValidate(
        randomUUID(),
        List.of(),
        description
      )
    );

    this.userClient.execute(
      new NPUCommandToolExecutionDescriptionPut(randomUUID(), description)
    );

    {
      final var r =
        this.userClient.execute(
          new NPUCommandToolExecutionDescriptionGet(randomUUID(), identifier)
        );

      assertEquals(description, r.execution().orElseThrow());
    }

    {
      final var r =
        this.userClient.execute(
          new NPUCommandToolExecutionDescriptionSearchBegin(
            randomUUID(),
            new NPToolExecutionDescriptionSearchParameters(
              new NPComparisonExactType.Anything<>(),
              1000L)
          )
        );

      assertEquals(
        description.summary(),
        r.results().items().get(0)
      );

      this.userClient.execute(
        new NPUCommandToolExecutionDescriptionSearchNext(randomUUID())
      );
      this.userClient.execute(
        new NPUCommandToolExecutionDescriptionSearchPrevious(randomUUID())
      );
    }
  }

  /**
   * Connected users can be listed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUsersConnected()
    throws Exception
  {
    setupUser(
      IDSTORE_FIXTURE.userWithLoginId(),
      IDSTORE_FIXTURE.userWithLoginName(),
      Set.of(LOGIN, USERS_READER)
    );

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      IDSTORE_FIXTURE.userWithLoginName(),
      IDSTORE_FIXTURE.password()
    );

    final var r =
      this.userClient.execute(new NPUCommandUsersConnected(randomUUID()));

    assertTrue(r.users().size() >= 1);
  }

  /**
   * Connected agents can be listed.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentsConnected()
    throws Exception
  {
    setupUser(
      IDSTORE_FIXTURE.userWithLoginId(),
      IDSTORE_FIXTURE.userWithLoginName(),
      Set.of(LOGIN, AGENTS_READER)
    );

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      IDSTORE_FIXTURE.userWithLoginName(),
      IDSTORE_FIXTURE.password()
    );

    final var r =
      this.userClient.execute(new NPUCommandAgentsConnected(randomUUID()));

    assertEquals(0, r.agents().size());
  }

  private static void setupUser(
    final UUID userId,
    final IdName userName,
    final Set<NPSecRole> roles)
    throws Exception
  {
    final var connection =
      SERVER_FIXTURE.databaseConnection();
    final var transaction =
      connection.openTransaction();

    transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
      .execute(
        new NPUser(
          userId,
          userName,
          new MSubject(
            roles.stream()
              .map(NPSecRole::role)
              .collect(Collectors.toUnmodifiableSet())
          )
        )
      );

    transaction.commit();
  }
}
