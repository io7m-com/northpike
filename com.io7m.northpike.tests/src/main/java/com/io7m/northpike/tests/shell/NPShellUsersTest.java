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

import com.io7m.idstore.model.IdName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.user.NPUCommandSelf;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchPrevious;
import com.io7m.northpike.protocol.user.NPUResponseSelf;
import com.io7m.northpike.protocol.user.NPUResponseUserSearch;
import com.io7m.northpike.shell.NPShellConfiguration;
import com.io7m.northpike.shell.NPShellType;
import com.io7m.northpike.shell.NPShells;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.api.NPUserClientFactoryType;
import com.io7m.northpike.user_client.api.NPUserClientType;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;
import org.mockito.Mockito;
import org.mockito.internal.verification.AtLeast;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.isA;

@Timeout(30L)
public final class NPShellUsersTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPShellUsersTest.class);

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
  public void setup(final @TempDir Path directory)
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
        directory,
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
  public void testSelf()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandSelf.class))
    ).thenReturn(new NPUResponseSelf(
      UUID.randomUUID(),
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("self");
    w.println("set --formatter RAW");
    w.println("self");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandSelf.class));
  }

  @Test
  public void testUserSearch()
    throws Exception
  {
    final var user =
      new NPUser(
        UUID.randomUUID(),
        new IdName("user"),
        new MSubject(
          Arrays.stream(NPSecRole.values())
            .map(NPSecRole::role)
            .collect(Collectors.toUnmodifiableSet())
        )
      );

    final var page =
      new NPPage<>(List.of(user, user, user), 1, 1, 0L);

    Mockito.when(
      this.userClient.execute(isA(NPUCommandUserSearchBegin.class))
    ).thenReturn(new NPUResponseUserSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandUserSearchNext.class))
    ).thenReturn(new NPUResponseUserSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandUserSearchPrevious.class))
    ).thenReturn(new NPUResponseUserSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.println("user-search-begin");
    w.println("user-search-next");
    w.println("user-search-previous");

    w.println("user-search-begin --name-equal-to user");
    w.println("user-search-begin --name-not-equal-to user");
    w.println("user-search-begin --name-similar-to user");
    w.println("user-search-begin --name-not-similar-to user");

    w.println("user-search-begin --roles-equal-to users.reader,users.writer");
    w.println("user-search-begin --roles-not-equal-to users.reader,users.writer");
    w.println("user-search-begin --roles-subset-of users.reader,users.writer");
    w.println("user-search-begin --roles-superset-of users.reader,users.writer");
    w.println("user-search-begin --roles-overlapping users.reader,users.writer");

    w.println("set --formatter RAW");

    w.println("user-search-begin");
    w.println("user-search-next");
    w.println("user-search-previous");

    w.println("user-search-begin --name-equal-to user");
    w.println("user-search-begin --name-not-equal-to user");
    w.println("user-search-begin --name-similar-to user");
    w.println("user-search-begin --name-not-similar-to user");

    w.println("user-search-begin --roles-equal-to users.reader,users.writer");
    w.println("user-search-begin --roles-not-equal-to users.reader,users.writer");
    w.println("user-search-begin --roles-subset-of users.reader,users.writer");
    w.println("user-search-begin --roles-superset-of users.reader,users.writer");
    w.println("user-search-begin --roles-overlapping users.reader,users.writer");

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(10))
      .execute(isA(NPUCommandUserSearchBegin.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandUserSearchNext.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandUserSearchPrevious.class));
  }

}
