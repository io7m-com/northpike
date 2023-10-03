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

import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.model.plans.NPPlanSummary;
import com.io7m.northpike.protocol.user.NPUCommandPlanDelete;
import com.io7m.northpike.protocol.user.NPUCommandPlanGet;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandPlanValidate;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponsePlanGet;
import com.io7m.northpike.protocol.user.NPUResponsePlanSearch;
import com.io7m.northpike.protocol.user.NPUResponsePlanValidate;
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

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.model.NPCompilationMessage.Kind.ERROR;
import static com.io7m.northpike.model.NPCompilationMessage.Kind.INFO;
import static com.io7m.northpike.model.NPCompilationMessage.Kind.WARNING;
import static java.nio.charset.StandardCharsets.UTF_8;
import static org.apache.commons.text.StringEscapeUtils.escapeJava;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.isA;

@Timeout(30L)
public final class NPShellPlansTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPShellPlansTest.class);

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
  public void testPlanValidate(
    final @TempDir Path directory)
    throws Exception
  {
    final var response =
      new NPUResponsePlanValidate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        List.of(
          new NPCompilationMessage(ERROR, 1, 1, "E 1 1"),
          new NPCompilationMessage(INFO, 2, 2, "I 2 2"),
          new NPCompilationMessage(WARNING, 3, 3, "W 3 3")
        )
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanValidate.class))
    ).thenReturn(response);

    final var data =
      Files.writeString(directory.resolve("file.txt"), "Data!");
    final var pathEscaped =
      escapeJava(escapeJava(data.toString()));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("plan-validate ");
    w.print("  --file ");
    w.print(pathEscaped);
    w.print("  --format-name format ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandPlanValidate.class));
  }

  @Test
  public void testPlanPut(
    final @TempDir Path directory)
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanPut.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var data =
      Files.writeString(directory.resolve("file.txt"), "Data!");
    final var pathEscaped =
      escapeJava(escapeJava(data.toString()));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("plan-put ");
    w.print("  --file ");
    w.print(pathEscaped);
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.print("  --format-name format ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandPlanPut.class));
  }

  @Test
  public void testPlanGet()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanGet.class))
    ).thenReturn(new NPUResponsePlanGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(
        new NPPlanDescriptionUnparsed(
          new NPPlanIdentifier(
            NPPlanName.of("com.io7m.example"),
            3L
          ),
          NPFormatName.of("format"),
          "Data!"
        )
      )
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("plan-get ");
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.println();

    w.println("set --formatter RAW");
    w.print("plan-get ");
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandPlanGet.class));
  }

  @Test
  public void testPlanSearch()
    throws Exception
  {
    final var page =
      new NPPage<>(
        List.of(
          new NPPlanSummary(
            new NPPlanIdentifier(
              NPPlanName.of("com.io7m.example"),
              3L
            ),
            "Plan 1"
          ),
          new NPPlanSummary(
            new NPPlanIdentifier(
              NPPlanName.of("com.io7m.example"),
              4L
            ),
            "Plan 2"
          ),
          new NPPlanSummary(
            new NPPlanIdentifier(
              NPPlanName.of("com.io7m.example"),
              5L
            ),
            "Plan 3"
          )
        ),
        1,
        1,
        0L
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanSearchBegin.class))
    ).thenReturn(new NPUResponsePlanSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanSearchNext.class))
    ).thenReturn(new NPUResponsePlanSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanSearchPrevious.class))
    ).thenReturn(new NPUResponsePlanSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.println("plan-search-begin --name-equal-to label2");
    w.println("plan-search-begin --name-not-equal-to label2");
    w.println("plan-search-begin --name-similar-to label2");
    w.println("plan-search-begin --name-not-similar-to label2");
    w.println("plan-search-begin --description-equal-to label2");
    w.println("plan-search-begin --description-not-equal-to label2");
    w.println("plan-search-begin --description-similar-to label2");
    w.println("plan-search-begin --description-not-similar-to label2");
    w.println("plan-search-begin");
    w.println("plan-search-next");
    w.println("plan-search-previous");

    w.println("set --formatter RAW");

    w.println("plan-search-begin --name-equal-to label2");
    w.println("plan-search-begin --name-not-equal-to label2");
    w.println("plan-search-begin --name-similar-to label2");
    w.println("plan-search-begin --name-not-similar-to label2");
    w.println("plan-search-begin --description-equal-to label2");
    w.println("plan-search-begin --description-not-equal-to label2");
    w.println("plan-search-begin --description-similar-to label2");
    w.println("plan-search-begin --description-not-similar-to label2");
    w.println("plan-search-begin");
    w.println("plan-search-next");
    w.println("plan-search-previous");

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(18))
      .execute(isA(NPUCommandPlanSearchBegin.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandPlanSearchNext.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandPlanSearchPrevious.class));
  }

  @Test
  public void testPlanDelete()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandPlanDelete.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("plan-delete ");
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.println();

    w.println("set --formatter RAW");
    w.print("plan-delete ");
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandPlanDelete.class));
  }
}
