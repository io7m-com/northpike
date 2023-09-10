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
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositorySearchParameters;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
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
import com.io7m.northpike.protocol.user.cb.NPU1Messages;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.containers.NPTestContainerInstances;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.northpike.toolexec.NPTXFormats;
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
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.model.security.NPSecRole.LOGIN;
import static com.io7m.northpike.model.security.NPSecRole.REPOSITORIES_READER;
import static com.io7m.northpike.model.security.NPSecRole.REPOSITORIES_WRITER;
import static com.io7m.northpike.model.security.NPSecRole.TOOLS_READER;
import static com.io7m.northpike.model.security.NPSecRole.TOOLS_WRITER;
import static com.io7m.northpike.tls.NPTLSDisabled.TLS_DISABLED;
import static java.util.Optional.empty;
import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

@Timeout(30L)
@ExtendWith({ErvillaExtension.class, ZeladorExtension.class})
@ErvillaConfiguration(projectName = "com.io7m.northpike", disabledIfUnsupported = true)
public final class NPUserClientTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPUserClientTest.class);

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private static NPTestContainers.NPIdstoreFixture IDSTORE_FIXTURE;
  private static NPTestContainers.NPServerFixture SERVER_FIXTURE;

  private ServerSocket socket;
  private NPStrings strings;
  private ExecutorService executor;
  private CountDownLatch serverCloseLatch;
  private CountDownLatch serverAcceptLatch;
  private NPUserClientConfiguration configuration;
  private NPUserClients users;
  private NPUserClientType userClient;
  private InetSocketAddress serverAddress;
  private IdName userName;
  private String userPassword;

  @BeforeAll
  public static void setupOnce(
    final @ErvillaCloseAfterSuite EContainerSupervisorType containers)
    throws Exception
  {
    IDSTORE_FIXTURE =
      NPTestContainerInstances.idstore(containers);
    SERVER_FIXTURE =
      NPTestContainerInstances.server(containers);
  }

  @BeforeEach
  public void setup()
    throws Exception
  {
    IDSTORE_FIXTURE.reset();
    SERVER_FIXTURE.reset();
    SERVER_FIXTURE.start();

    this.executor =
      Executors.newSingleThreadExecutor();
    this.serverAcceptLatch =
      new CountDownLatch(1);
    this.serverCloseLatch =
      new CountDownLatch(1);

    this.strings =
      NPStrings.create(Locale.ROOT);

    this.socket =
      ServerSocketFactory.getDefault()
        .createServerSocket();

    this.socket.setReuseAddress(true);
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

    this.userName =
      new IdName("user0");
    this.userPassword =
      "12345678";

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
    SERVER_FIXTURE.reset();

    this.userClient.close();
    this.socket.close();
    this.serverCloseLatch.await(10L, TimeUnit.SECONDS);
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
      } finally {
        this.serverCloseLatch.countDown();
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
          this.userName,
          this.userPassword
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
    final var id =
      IDSTORE_FIXTURE.createUser(this.userName.value());

    final var connection =
      SERVER_FIXTURE.databaseConnection();
    final var transaction =
      connection.openTransaction();

    transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
      .execute(new NPUser(id, this.userName, new MSubject(Set.of())));

    transaction.commit();

    final var ex =
      assertThrows(NPUserClientException.class, () -> {
        this.userClient.login(
          this.serverAddress,
          TLS_DISABLED,
          this.userName,
          this.userPassword
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
    this.setupUser(Set.of(LOGIN));

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      this.userName,
      this.userPassword
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
    this.setupUser(Set.of(LOGIN, REPOSITORIES_WRITER, REPOSITORIES_READER));

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      this.userName,
      this.userPassword
    );

    final var repository =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        randomUUID(),
        URI.create("http://www.example.com"),
        CREDENTIALS_NONE
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
    this.setupUser(Set.of(LOGIN, REPOSITORIES_WRITER, REPOSITORIES_READER));

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      this.userName,
      this.userPassword
    );

    final var repository0 =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        randomUUID(),
        URI.create("http://www.example.com/0"),
        CREDENTIALS_NONE
      );

    final var repository1 =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        randomUUID(),
        URI.create("http://www.example.com/1"),
        CREDENTIALS_NONE
      );

    final var repository2 =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        randomUUID(),
        URI.create("http://www.example.com/2"),
        CREDENTIALS_NONE
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
          randomUUID(), new NPRepositorySearchParameters()));

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
    this.setupUser(Set.of(LOGIN, TOOLS_WRITER, TOOLS_READER));

    this.userClient.login(
      this.serverAddress,
      TLS_DISABLED,
      this.userName,
      this.userPassword
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
        NPTXFormats.nptx1(),
        """
          <?xml version="1.0" encoding="UTF-8" ?>
          <ToolExecution xmlns="urn:com.io7m.northpike.toolexec:1"
                         Name="com.io7m.ex0"
                         Version="1">
            <ArgumentAdd Value="ok"/>
          </ToolExecution>
                    """.strip()
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
            new NPToolExecutionDescriptionSearchParameters(empty()))
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


  private void setupUser(
    final Set<NPSecRole> roles)
    throws Exception
  {
    final var id =
      IDSTORE_FIXTURE.createUser(this.userName.value());

    final var connection =
      SERVER_FIXTURE.databaseConnection();
    final var transaction =
      connection.openTransaction();

    transaction.queries(NPDatabaseQueriesUsersType.PutType.class)
      .execute(
        new NPUser(
          id,
          this.userName,
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
