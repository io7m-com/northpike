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

import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionPut;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionSearch;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionValidate;
import com.io7m.northpike.shell.NPShellConfiguration;
import com.io7m.northpike.shell.NPShellType;
import com.io7m.northpike.shell.NPShells;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.api.NPUserClientFactoryType;
import com.io7m.northpike.user_client.api.NPUserClientType;
import com.io7m.seltzer.api.SStructuredError;
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
import java.util.Map;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.apache.commons.text.StringEscapeUtils.escapeJava;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.isA;

@Timeout(30L)
public final class NPShellToolExecutionsTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPShellToolExecutionsTest.class);

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
  public void testToolExecutionValidate(
    final @TempDir Path directory)
    throws Exception
  {
    final var response =
      new NPUResponseToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        UUID.randomUUID(),
        List.of(
          new SStructuredError<>(
            "error",
            "ERROR!",
            Map.of("x", "y"),
            Optional.empty(),
            Optional.empty()
          )
        )
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandToolExecutionDescriptionValidate.class))
    ).thenReturn(response);

    final var data =
      Files.writeString(directory.resolve("file.txt"), "Data!");
    final var pathEscaped =
      escapeJava(escapeJava(data.toString()));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("tool-execution-validate ");
    w.print("  --file ");
    w.print(pathEscaped);
    w.print("  --format-name format ");
    w.print("  --variable-boolean com.io7m.b0 ");
    w.print("  --variable-integer com.io7m.i0 ");
    w.print("  --variable-string com.io7m.s0 ");
    w.print("  --variable-string-set com.io7m.ss0 ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandToolExecutionDescriptionValidate.class));
  }

  @Test
  public void testToolExecutionPut(
    final @TempDir Path directory)
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandToolExecutionDescriptionPut.class))
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
    w.print("tool-execution-put ");
    w.print("  --file ");
    w.print(pathEscaped);
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.print("  --format-name format ");
    w.print("  --tool com.io7m.tool ");
    w.print("  --description Something ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandToolExecutionDescriptionPut.class));
  }

  @Test
  public void testToolExecutionGet()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandToolExecutionDescriptionGet.class))
    ).thenReturn(new NPUResponseToolExecutionDescriptionGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(
        new NPToolExecutionDescription(
          new NPToolExecutionIdentifier(
            NPToolExecutionName.of("com.io7m.example"),
            3L
          ),
          NPToolName.of("com.io7m.tool"),
          "Something",
          NPFormatName.of("format"),
          "Data!"
        )
      )
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("tool-execution-get ");
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.println();

    w.println("set --formatter RAW");
    w.print("tool-execution-get ");
    w.print("  --name com.io7m.example ");
    w.print("  --version 3 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandToolExecutionDescriptionGet.class));
  }

  @Test
  public void testToolExecutionSearch()
    throws Exception
  {
    final var page =
      new NPPage<>(
        List.of(
          new NPToolExecutionDescriptionSummary(
            new NPToolExecutionIdentifier(
              NPToolExecutionName.of("com.io7m.example"),
              3L
            ),
            NPToolName.of("com.io7m.tool"),
            "Execution 1"
          ),
          new NPToolExecutionDescriptionSummary(
            new NPToolExecutionIdentifier(
              NPToolExecutionName.of("com.io7m.example"),
              4L
            ),
            NPToolName.of("com.io7m.tool"),
            "Execution 2"
          ),
          new NPToolExecutionDescriptionSummary(
            new NPToolExecutionIdentifier(
              NPToolExecutionName.of("com.io7m.example"),
              5L
            ),
            NPToolName.of("com.io7m.tool"),
            "Execution 3"
          )
        ),
        1,
        1,
        0L
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandToolExecutionDescriptionSearchBegin.class))
    ).thenReturn(new NPUResponseToolExecutionDescriptionSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandToolExecutionDescriptionSearchNext.class))
    ).thenReturn(new NPUResponseToolExecutionDescriptionSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandToolExecutionDescriptionSearchPrevious.class))
    ).thenReturn(new NPUResponseToolExecutionDescriptionSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.println("tool-execution-search-begin");
    w.println("tool-execution-search-next");
    w.println("tool-execution-search-previous");

    w.println("tool-execution-search-begin --tool-equal-to com.io7m.example");
    w.println("tool-execution-search-begin --tool-not-equal-to com.io7m.example");
    w.println("tool-execution-search-next");
    w.println("tool-execution-search-previous");

    w.println("set --formatter RAW");

    w.println("tool-execution-search-begin");
    w.println("tool-execution-search-next");
    w.println("tool-execution-search-previous");

    w.println("tool-execution-search-begin --tool-equal-to com.io7m.example");
    w.println("tool-execution-search-begin --tool-not-equal-to com.io7m.example");
    w.println("tool-execution-search-next");
    w.println("tool-execution-search-previous");

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(6))
      .execute(isA(NPUCommandToolExecutionDescriptionSearchBegin.class));
    Mockito.verify(this.userClient, new AtLeast(4))
      .execute(isA(NPUCommandToolExecutionDescriptionSearchNext.class));
    Mockito.verify(this.userClient, new AtLeast(4))
      .execute(isA(NPUCommandToolExecutionDescriptionSearchPrevious.class));
  }
}
