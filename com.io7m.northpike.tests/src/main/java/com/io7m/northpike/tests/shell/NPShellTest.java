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


package com.io7m.northpike.tests.shell;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.keys.NPPublicKeys;
import com.io7m.northpike.model.NPAuditEvent;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.protocol.user.NPUCommandAuditSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAuditSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAuditSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyDelete;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyGet;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyPut;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryGet;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeyAssign;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeyUnassign;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeysAssigned;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandSCMProvidersSupported;
import com.io7m.northpike.protocol.user.NPUResponseAuditSearch;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponsePublicKeyGet;
import com.io7m.northpike.protocol.user.NPUResponsePublicKeySearch;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryGet;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryPublicKeysAssigned;
import com.io7m.northpike.protocol.user.NPUResponseRepositorySearch;
import com.io7m.northpike.protocol.user.NPUResponseSCMProvidersSupported;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.shell.NPShellConfiguration;
import com.io7m.northpike.shell.NPShellType;
import com.io7m.northpike.shell.NPShells;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.keys.NPPublicKeysTest;
import com.io7m.northpike.user_client.api.NPUserClientException;
import com.io7m.northpike.user_client.api.NPUserClientFactoryType;
import com.io7m.northpike.user_client.api.NPUserClientType;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;
import org.mockito.Mockito;
import org.mockito.internal.verification.Times;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;

@Timeout(30L)
public final class NPShellTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPShellTest.class);

  private NPShells shells;
  private NPUserClientFactoryType userClients;
  private NPUserClientType userClient;
  private NPFakeTerminal terminal;
  private volatile NPShellType shell;
  private ExecutorService executor;
  private CountDownLatch latchShutdown;
  private int exitCode;
  private NPShellConfiguration shellConfiguration;
  private CountDownLatch latchStartup;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.userClients =
      Mockito.mock(NPUserClientFactoryType.class);
    this.userClient =
      Mockito.mock(NPUserClientType.class);

    Mockito.when(this.userClients.createUserClient(any()))
      .thenReturn(this.userClient);

    this.terminal =
      new NPFakeTerminal();
    this.executor =
      Executors.newFixedThreadPool(1);

    this.latchStartup =
      new CountDownLatch(1);
    this.latchShutdown =
      new CountDownLatch(1);
    this.exitCode = 0;

    this.shells =
      new NPShells();

    this.shellConfiguration =
      new NPShellConfiguration(
        Locale.ROOT,
        this.userClients,
        NPStrings.create(Locale.ROOT),
        Optional.of(this.terminal),
        1_000_000
      );

    this.executor.execute(() -> {
      LOG.debug("Starting shell");
      try (var shell = this.shells.create(this.shellConfiguration)) {
        this.shell = shell;
        this.latchStartup.countDown();
        shell.run();
      } catch (final Throwable e) {
        LOG.debug("Shell failed: ", e);
        throw new RuntimeException(e);
      } finally {
        LOG.debug("Finished shell");
        this.exitCode = this.shell.exitCode();
        this.latchShutdown.countDown();
      }
    });

    this.latchStartup.await(5L, TimeUnit.SECONDS);
  }

  private void waitForShell()
    throws InterruptedException
  {
    this.latchShutdown.await(3L, TimeUnit.SECONDS);
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.executor.shutdown();
    this.executor.awaitTermination(3L, TimeUnit.SECONDS);

    final var out =
      this.terminal.terminalProducedOutput();

    System.out.println(out.toString(UTF_8));
  }

  @Test
  public void testShellHelp()
    throws Exception
  {
    final var commandNames =
      this.shell.commands()
        .stream()
        .map(c -> c.metadata().name())
        .collect(Collectors.toUnmodifiableSet());

    final var w = this.terminal.sendInputToTerminalWriter();
    for (final var name : commandNames) {
      w.printf("help %s%n", name);
    }
    w.println("help");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testShellVersion()
    throws Exception
  {
    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("version");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testShellLogin()
    throws Exception
  {
    final var w = this.terminal.sendInputToTerminalWriter();
    w.println(
      "login --user nobody --password 1234 --server localhost --port 30000");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testShellLoginFails()
    throws Exception
  {
    Mockito.doThrow(
        new NPUserClientException("x", errorIo(), Map.of(), Optional.empty())
      ).when(this.userClient)
      .login(any(), any(), any(), any());

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println(
      "login --user nobody --password 1234 --server localhost --port 30000");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(1, this.exitCode);
  }

  @Test
  public void testShellLogout()
    throws Exception
  {
    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("logout");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new Times(2))
      .close();
  }

  @Test
  public void testShellAuditSearch()
    throws Exception
  {
    final var response =
      new NPUResponseAuditSearch(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPPage<>(
          List.of(
            new NPAuditEvent(
              0L,
              OffsetDateTime.now(),
              new NPAuditUserOrAgentType.User(UUID.randomUUID()),
              "TYPE_1",
              Map.of()
            ),
            new NPAuditEvent(
              1L,
              OffsetDateTime.now(),
              new NPAuditUserOrAgentType.User(UUID.randomUUID()),
              "TYPE_1",
              Map.of()
            ),
            new NPAuditEvent(
              2L,
              OffsetDateTime.now(),
              new NPAuditUserOrAgentType.User(UUID.randomUUID()),
              "TYPE_1",
              Map.of()
            )
          ),
          1,
          1,
          0L
        )
      );

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandAuditSearchBegin.class))
    ).thenReturn(response);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandAuditSearchNext.class))
    ).thenReturn(response);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandAuditSearchPrevious.class))
    ).thenReturn(response);

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("audit-search-begin");
    w.println("audit-search-next");
    w.println("audit-search-previous");
    w.println("set --formatter RAW");
    w.println("audit-search-begin");
    w.println("audit-search-next");
    w.println("audit-search-previous");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testRepositoryPutGet()
    throws Exception
  {
    final var id =
      UUID.randomUUID();
    final var uri =
      URI.create("http://www.example.com");

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositoryPut.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var repository =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        new NPRepositoryID(id),
        uri,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE,
        REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS
      );

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositoryGet.class))
    ).thenReturn(new NPUResponseRepositoryGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(repository)
    ));

    final var searchResponse =
      new NPUResponseRepositorySearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      new NPPage<>(
        List.of(
          repository.summary(),
          repository.summary(),
          repository.summary()
        ),
        1,
        1,
        0L
      )
    );

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositorySearchBegin.class))
    ).thenReturn(searchResponse);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositorySearchNext.class))
    ).thenReturn(searchResponse);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositorySearchPrevious.class))
    ).thenReturn(searchResponse);

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("repository-put ");
    w.print(" --id ");
    w.print(id);
    w.print(" --provider ");
    w.print(NPSCMRepositoriesJGit.providerNameGet());
    w.print(" --uri ");
    w.print(uri);
    w.print(" --credentials ");
    w.print("none");
    w.print(" --signing-policy ");
    w.print(REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS);
    w.println();

    w.print("repository-get ");
    w.print(" --id ");
    w.print(id);
    w.println();

    w.println("repository-search-begin");
    w.println("repository-search-next");
    w.println("repository-search-previous");

    w.println("set --formatter RAW");

    w.print("repository-get ");
    w.print(" --id ");
    w.print(id);
    w.println();

    w.println("repository-search-begin");
    w.println("repository-search-next");
    w.println("repository-search-previous");

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testPublicKeyPutGet(
    final @TempDir Path directory)
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandPublicKeyPut.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var publicKey =
      NPPublicKeys.decodeString(NPPublicKeysTest.KEY_TEXT).get(0);

    final var keyFile = directory.resolve("key.txt");
    Files.writeString(keyFile, publicKey.encodedForm(), UTF_8);

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandPublicKeyGet.class))
    ).thenReturn(new NPUResponsePublicKeyGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(publicKey.encodedForm())
    ));

    final var searchResponse =
      new NPUResponsePublicKeySearch(
        UUID.randomUUID(),
        UUID.randomUUID(),
        new NPPage<>(
          List.of(
            publicKey.encodedForm(),
            publicKey.encodedForm(),
            publicKey.encodedForm()
          ),
          1,
          1,
          0L
        )
      );

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandPublicKeySearchBegin.class))
    ).thenReturn(searchResponse);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandPublicKeySearchNext.class))
    ).thenReturn(searchResponse);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandPublicKeySearchPrevious.class))
    ).thenReturn(searchResponse);
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandPublicKeyDelete.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("public-key-put ");
    w.print(" --file ");
    w.print(keyFile);
    w.println();

    w.print("public-key-get ");
    w.print(" --fingerprint ");
    w.print(publicKey.fingerprint().value());
    w.println();

    w.println("public-key-search-begin");
    w.println("public-key-search-next");
    w.println("public-key-search-previous");

    w.println("set --formatter RAW");

    w.print("public-key-get ");
    w.print(" --fingerprint ");
    w.print(publicKey.fingerprint().value());
    w.println();

    w.println("public-key-search-begin");
    w.println("public-key-search-next");
    w.println("public-key-search-previous");

    w.println("public-key-delete --fingerprint " + publicKey.fingerprint());

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testRepositoryKeys()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositoryPublicKeyAssign.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositoryPublicKeyUnassign.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandRepositoryPublicKeysAssigned.class))
    ).thenReturn(new NPUResponseRepositoryPublicKeysAssigned(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Set.of(
        new NPFingerprint("1dce17634eaaa91013f0e722835ebea6d80c9656"),
        new NPFingerprint("01c795300b82ed5a9fe02448589e4945f9fb2f09"),
        new NPFingerprint("fa2e21344c1a75831b71fc029d17726b8eff26d7")
      )
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("repository-public-key-assign ");
    w.print(" --repository 8ad0c901-6950-460f-ad80-f10c3493122c");
    w.print(" --key da39a3ee5e6b4b0d3255bfef95601890afd80709");
    w.println();

    w.print("repository-public-key-unassign ");
    w.print(" --repository 8ad0c901-6950-460f-ad80-f10c3493122c");
    w.print(" --key da39a3ee5e6b4b0d3255bfef95601890afd80709");
    w.println();

    w.print("repository-public-keys-assigned ");
    w.print(" --repository 8ad0c901-6950-460f-ad80-f10c3493122c");
    w.println();

    w.println("set --formatter RAW");

    w.print("repository-public-key-assign ");
    w.print(" --repository 8ad0c901-6950-460f-ad80-f10c3493122c");
    w.print(" --key da39a3ee5e6b4b0d3255bfef95601890afd80709");
    w.println();

    w.print("repository-public-key-unassign ");
    w.print(" --repository 8ad0c901-6950-460f-ad80-f10c3493122c");
    w.print(" --key da39a3ee5e6b4b0d3255bfef95601890afd80709");
    w.println();

    w.print("repository-public-keys-assigned ");
    w.print(" --repository 8ad0c901-6950-460f-ad80-f10c3493122c");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }

  @Test
  public void testSCMProviders()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(Mockito.isA(NPUCommandSCMProvidersSupported.class))
    ).thenReturn(new NPUResponseSCMProvidersSupported(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Set.of(
        new NPSCMProviderDescription(
          new RDottedName("x.y.a"),
          "An SCM provider of some sort.",
          URI.create("https://www.example.com/a")
        ),
        new NPSCMProviderDescription(
          new RDottedName("x.y.b"),
          "An SCM provider of some sort.",
          URI.create("https://www.example.com/b")
        ),
        new NPSCMProviderDescription(
          new RDottedName("x.y.c"),
          "An SCM provider of some sort.",
          URI.create("https://www.example.com/c")
        )
      )
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("scm-providers-supported");
    w.println("set --formatter RAW");
    w.println("scm-providers-supported");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);
  }
}
