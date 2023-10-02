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

import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabel;
import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.model.NPAgentSummary;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.protocol.user.NPUCommandAgentGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAgentPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchPrevious;
import com.io7m.northpike.protocol.user.NPUResponseAgentGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelSearch;
import com.io7m.northpike.protocol.user.NPUResponseAgentSearch;
import com.io7m.northpike.protocol.user.NPUResponseOK;
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
import org.mockito.Mockito;
import org.mockito.internal.verification.AtLeast;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.isA;

@Timeout(30L)
public final class NPShellAgentsTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPShellAgentsTest.class);

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
  public void testAgentPutGet()
    throws Exception
  {
    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "AgentExample",
        NPKey.parse(
          "8ea1b01d8fe352552e97cb727eee4f5a948a0919dc3f1d0c2f194c2aed52e4e1"),
        Map.ofEntries(
          Map.entry(
            "PATH",
            "/sbin:/bin:/usr/bin:/usr/sbin"
          )
        ),
        Map.ofEntries(
          Map.entry(
            "java.runtime.name",
            "OpenJDK Runtime Environment"
          )
        ),
        Map.ofEntries(
          Map.entry(
            NPAgentLabelName.of("label0"),
            new NPAgentLabel(NPAgentLabelName.of("label0"), "Label 0")
          ),
          Map.entry(
            NPAgentLabelName.of("label1"),
            new NPAgentLabel(NPAgentLabelName.of("label1"), "Label 1")
          ),
          Map.entry(
            NPAgentLabelName.of("label2"),
            new NPAgentLabel(NPAgentLabelName.of("label2"), "Label 2")
          )
        )
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentPut.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentGet.class))
    ).thenReturn(new NPUResponseAgentGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(agent)
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-put ");
    w.print(" --id e10f1d49-3e4c-40e3-81dd-b771a38ec243 ");
    w.print(" --name AgentExample ");
    w.print(
      " --access-key 8ea1b01d8fe352552e97cb727eee4f5a948a0919dc3f1d0c2f194c2aed52e4e1");
    w.println();

    w.print("agent-get ");
    w.print(" --id e10f1d49-3e4c-40e3-81dd-b771a38ec243 ");
    w.println();

    w.println("set --formatter RAW");

    w.print("agent-get ");
    w.print(" --id e10f1d49-3e4c-40e3-81dd-b771a38ec243 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentPut.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentGet.class));
  }

  @Test
  public void testAgentSearch()
    throws Exception
  {
    final var agent =
      new NPAgentSummary(
        new NPAgentID(UUID.randomUUID()),
        "AgentExample"
      );

    final var page =
      new NPPage<>(List.of(agent, agent, agent), 1, 1, 0L);

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentSearchBegin.class))
    ).thenReturn(new NPUResponseAgentSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentSearchNext.class))
    ).thenReturn(new NPUResponseAgentSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentSearchPrevious.class))
    ).thenReturn(new NPUResponseAgentSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.println("agent-search-begin");
    w.println("agent-search-next");
    w.println("agent-search-previous");

    w.println("agent-search-begin --labels-equal-to agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-not-equal-to agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-subset-of agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-superset-of agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-overlapping agents.reader,agents.writer");

    w.println("set --formatter RAW");

    w.println("agent-search-begin");
    w.println("agent-search-next");
    w.println("agent-search-previous");

    w.println("agent-search-begin --labels-equal-to agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-not-equal-to agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-subset-of agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-superset-of agents.reader,agents.writer");
    w.println(
      "agent-search-begin --labels-overlapping agents.reader,agents.writer");

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(10))
      .execute(isA(NPUCommandAgentSearchBegin.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentSearchNext.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentSearchPrevious.class));
  }

  @Test
  public void testAgentLabelPutGet()
    throws Exception
  {
    final var label =
      new NPAgentLabel(NPAgentLabelName.of("label2"), "Label 2");

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentLabelPut.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentLabelGet.class))
    ).thenReturn(new NPUResponseAgentLabelGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(label)
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-label-put ");
    w.print(" --name label2 ");
    w.print(" --description 'Label 2'");
    w.println();

    w.print("agent-label-get ");
    w.print(" --name label2 ");
    w.println();

    w.println("set --formatter RAW");

    w.print("agent-label-get ");
    w.print(" --name label2 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentLabelPut.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentLabelGet.class));
  }

  @Test
  public void testAgentLabelSearch()
    throws Exception
  {
    final var label =
      new NPAgentLabel(NPAgentLabelName.of("label2"), "Label 2");

    final var page =
      new NPPage<>(List.of(label, label, label), 1, 1, 0L);

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentLabelSearchBegin.class))
    ).thenReturn(new NPUResponseAgentLabelSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentLabelSearchNext.class))
    ).thenReturn(new NPUResponseAgentLabelSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentLabelSearchPrevious.class))
    ).thenReturn(new NPUResponseAgentLabelSearch(
      UUID.randomUUID(),
      UUID.randomUUID(),
      page
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.println("agent-label-search-begin");
    w.println("agent-label-search-next");
    w.println("agent-label-search-previous");

    w.println("agent-label-search-begin --name-equal-to label2");
    w.println("agent-label-search-begin --name-not-equal-to label2");
    w.println("agent-label-search-begin --name-similar-to label2");
    w.println("agent-label-search-begin --name-not-similar-to label2");
    w.println("agent-label-search-begin --description-equal-to label2");
    w.println("agent-label-search-begin --description-not-equal-to label2");
    w.println("agent-label-search-begin --description-similar-to label2");
    w.println("agent-label-search-begin --description-not-similar-to label2");

    w.println("set --formatter RAW");

    w.println("agent-label-search-begin");
    w.println("agent-label-search-next");
    w.println("agent-label-search-previous");

    w.println("agent-label-search-begin --name-equal-to label2");
    w.println("agent-label-search-begin --name-not-equal-to label2");
    w.println("agent-label-search-begin --name-similar-to label2");
    w.println("agent-label-search-begin --name-not-similar-to label2");
    w.println("agent-label-search-begin --description-equal-to label2");
    w.println("agent-label-search-begin --description-not-equal-to label2");
    w.println("agent-label-search-begin --description-similar-to label2");
    w.println("agent-label-search-begin --description-not-similar-to label2");

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(10))
      .execute(isA(NPUCommandAgentLabelSearchBegin.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentLabelSearchNext.class));
    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentLabelSearchPrevious.class));
  }

  @Test
  public void testAgentLabelDelete()
    throws Exception
  {
    final var label =
      new NPAgentLabel(NPAgentLabelName.of("label2"), "Label 2");

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentLabelDelete.class))
    ).thenReturn(new NPUResponseOK(
      UUID.randomUUID(),
      UUID.randomUUID()
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-label-delete ");
    w.print(" --name label2 ");
    w.println();

    w.println("set --formatter RAW");

    w.print("agent-label-delete ");
    w.print(" --name label2 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(2))
      .execute(isA(NPUCommandAgentLabelDelete.class));
  }

  @Test
  public void testAgentLabelAssignNonexistent()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentGet.class))
    ).thenReturn(new NPUResponseAgentGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.empty()
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-label-assign ");
    w.print(" --agent d5247381-e96c-436f-b378-1072edb0f534 ");
    w.print(" --label label2 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(1, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentGet.class));
  }

  @Test
  public void testAgentLabelUnassignNonexistent()
    throws Exception
  {
    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentGet.class))
    ).thenReturn(new NPUResponseAgentGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.empty()
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-label-unassign ");
    w.print(" --agent d5247381-e96c-436f-b378-1072edb0f534 ");
    w.print(" --label label2 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(1, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentGet.class));
  }

  @Test
  public void testAgentLabelAssign()
    throws Exception
  {
    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent0",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentGet.class))
    ).thenReturn(new NPUResponseAgentGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(agent)
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-label-assign ");
    w.print(" --agent d5247381-e96c-436f-b378-1072edb0f534 ");
    w.print(" --label label2 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentGet.class));
    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentPut.class));
  }

  @Test
  public void testAgentLabelUnassign()
    throws Exception
  {
    final var agent =
      new NPAgentDescription(
        new NPAgentID(UUID.randomUUID()),
        "Agent0",
        NPKey.generate(),
        Map.of(),
        Map.of(),
        Map.of()
      );

    Mockito.when(
      this.userClient.execute(isA(NPUCommandAgentGet.class))
    ).thenReturn(new NPUResponseAgentGet(
      UUID.randomUUID(),
      UUID.randomUUID(),
      Optional.of(agent)
    ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");

    w.print("agent-label-unassign ");
    w.print(" --agent d5247381-e96c-436f-b378-1072edb0f534 ");
    w.print(" --label label2 ");
    w.println();

    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentGet.class));
    Mockito.verify(this.userClient, new AtLeast(1))
      .execute(isA(NPUCommandAgentPut.class));
  }
}
