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


package com.io7m.northpike.tests.agent.shell;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientException;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientFactoryType;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientType;
import com.io7m.northpike.agent.shell.NPAShellConfiguration;
import com.io7m.northpike.agent.shell.NPAShellType;
import com.io7m.northpike.agent.shell.NPAShells;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.agents.NPAgentServerSummary;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabled;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentServerAssign;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgentList;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.protocol.agent_console.NPACResponseServer;
import com.io7m.northpike.protocol.agent_console.NPACResponseServerList;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tests.shell.NPFakeTerminal;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.mockito.Mockito;
import org.mockito.internal.verification.AtLeast;
import org.mockito.internal.verification.Times;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.net.InetSocketAddress;
import java.nio.file.Paths;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.isA;

@Timeout(30L)
public final class NPAShellBasicTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAShellBasicTest.class);

  private NPAShells shells;
  private NPAConsoleClientFactoryType consoleClients;
  private NPAConsoleClientType consoleClient;
  private NPFakeTerminal terminal;
  private volatile NPAShellType shell;
  private ExecutorService executor;
  private CountDownLatch latchShutdown;
  private int exitCode;
  private NPAShellConfiguration shellConfiguration;
  private CountDownLatch latchStartup;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.consoleClients =
      Mockito.mock(NPAConsoleClientFactoryType.class);
    this.consoleClient =
      Mockito.mock(NPAConsoleClientType.class);

    Mockito.when(this.consoleClients.createConsoleClient(any()))
      .thenReturn(this.consoleClient);

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
      new NPAShells();

    this.shellConfiguration =
      new NPAShellConfiguration(
        Locale.ROOT,
        this.consoleClients,
        NPStrings.create(Locale.ROOT),
        Optional.of(this.terminal)
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
  public void testShellHelpNonexistent()
    throws Exception
  {
    final var w = this.terminal.sendInputToTerminalWriter();
    w.print("help nonexistent\n");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(1, this.exitCode);
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
      "login --access-key 1234 --agent localhost --port 30000");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new AtLeast(1))
      .login(
        eq(InetSocketAddress.createUnresolved("localhost", 30000)),
        eq("1234")
      );
  }

  @Test
  public void testShellLoginFails()
    throws Exception
  {
    Mockito.doThrow(
        new NPAConsoleClientException("x", errorIo(), Map.of(), Optional.empty())
      ).when(this.consoleClient)
      .login(any(), any());

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

    Mockito.verify(this.consoleClient, new Times(2))
      .close();
  }

  @Test
  public void testShellAgentCreate()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseOK(
        UUID.randomUUID(),
        UUID.randomUUID()
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("agent-create --name a");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellAgentDelete()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseOK(
        UUID.randomUUID(),
        UUID.randomUUID()
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("agent-delete --name a");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellAgentGet()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseAgent(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.of(
          new NPACResponseAgent.Result(
            NPAgentLocalName.of("a"),
            new NPAgentKeyPairFactoryEd448()
              .generateKeyPair()
              .publicKey(),
            Optional.of(new NPAgentServerID(UUID.randomUUID())),
            Optional.of(
              NPAWorkExecutorConfiguration.builder()
                .setExecutorType(new RDottedName("workexec.local"))
                .setWorkDirectory(Paths.get("/tmp/x"))
                .setTemporaryDirectory(Paths.get("/tmp/t"))
                .setContainerImage(new NPAWorkExecutorContainerImage(
                  "quay.io",
                  "io7mcom/idstore",
                  "1.0.0",
                  Optional.of("a3fc0f2ef34f6bbafdc9162f3d07a1f7dcdaa6544119081c")
                ))
                .build()
            )
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("set --formatter PRETTY");
    w.println("agent-get --name a");
    w.println("set --formatter RAW");
    w.println("agent-get --name a");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellAgentList()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseAgentList(
        UUID.randomUUID(),
        UUID.randomUUID(),
        List.of(
          NPAgentLocalName.of("a"),
          NPAgentLocalName.of("b"),
          NPAgentLocalName.of("c")
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("set --formatter PRETTY");
    w.println("agent-list");
    w.println("agent-list --offset a --limit 10");
    w.println("set --formatter RAW");
    w.println("agent-list");
    w.println("agent-list --offset a --limit 10");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerList()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseServerList(
        UUID.randomUUID(),
        UUID.randomUUID(),
        List.of(
          new NPAgentServerSummary(
            new NPAgentServerID(UUID.randomUUID()),
            "s1.example.com"
          ),
          new NPAgentServerSummary(
            new NPAgentServerID(UUID.randomUUID()),
            "s2.example.com"
          ),
          new NPAgentServerSummary(
            new NPAgentServerID(UUID.randomUUID()),
            "s3.example.com"
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("set --formatter PRETTY");
    w.println("server-list");
    w.println(
      "server-list --offset a753a5cb-e50d-4dcf-952c-27cb1898c66b --limit 10");
    w.println("set --formatter RAW");
    w.println("server-list");
    w.println(
      "server-list --offset a753a5cb-e50d-4dcf-952c-27cb1898c66b --limit 10");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerDelete()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseOK(
        UUID.randomUUID(),
        UUID.randomUUID()
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("server-delete --server a753a5cb-e50d-4dcf-952c-27cb1898c66b");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerGet()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(any()))
      .thenReturn(new NPACResponseServer(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.of(
          new NPAgentServerDescription(
            new NPAgentServerID(UUID.randomUUID()),
            "s1.example.com",
            20000,
            new NPTLSEnabled(
              new NPTLSStoreConfiguration(
                "CANONMILL",
                "CANONMILL",
                "changeit",
                Paths.get("/tmp/ks")
              ),
              new NPTLSStoreConfiguration(
                "CANONMILL",
                "CANONMILL",
                "changeit",
                Paths.get("/tmp/ts")
              )
            ),
            1_000_000
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.println("set --formatter PRETTY");
    w.println("server-get --server a753a5cb-e50d-4dcf-952c-27cb1898c66b");
    w.println("set --formatter RAW");
    w.println("server-get --server a753a5cb-e50d-4dcf-952c-27cb1898c66b");
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerPut0()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(isA(NPACCommandServerGet.class)))
      .thenReturn(new NPACResponseServer(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.empty()
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("server-put ");
    w.print(" --server a753a5cb-e50d-4dcf-952c-27cb1898c66b ");
    w.print(" --hostname s1.example.com ");
    w.print(" --port 40000 ");
    w.print(" --message-size-limit 1000 ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerGet.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerPut.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerPut1()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(isA(NPACCommandServerGet.class)))
      .thenReturn(new NPACResponseServer(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.of(
          new NPAgentServerDescription(
            new NPAgentServerID(UUID.fromString("a753a5cb-e50d-4dcf-952c-27cb1898c66b")),
            "s2.example.com",
            50000,
            NPTLSDisabled.TLS_DISABLED,
            1_000_000
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("server-put ");
    w.print(" --server a753a5cb-e50d-4dcf-952c-27cb1898c66b ");
    w.print(" --hostname s1.example.com ");
    w.print(" --port 40000 ");
    w.print(" --message-size-limit 1000 ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerGet.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerPut.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerSetTLS0()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(isA(NPACCommandServerGet.class)))
      .thenReturn(new NPACResponseServer(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.of(
          new NPAgentServerDescription(
            new NPAgentServerID(UUID.fromString("a753a5cb-e50d-4dcf-952c-27cb1898c66b")),
            "s2.example.com",
            50000,
            NPTLSDisabled.TLS_DISABLED,
            1_000_000
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("server-set-tls ");
    w.print(" --server a753a5cb-e50d-4dcf-952c-27cb1898c66b ");
    w.print(" --enabled true ");
    w.print(" --key-store-type CANONMILL ");
    w.print(" --key-store-provider CANONMILL ");
    w.print(" --key-store-password changeit ");
    w.print(" --key-store-path /tmp/p ");
    w.print(" --trust-store-type CANONMILL ");
    w.print(" --trust-store-provider CANONMILL ");
    w.print(" --trust-store-password changeit ");
    w.print(" --trust-store-path /tmp/p ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerGet.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerPut.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerSetTLS1()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(isA(NPACCommandServerGet.class)))
      .thenReturn(new NPACResponseServer(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.of(
          new NPAgentServerDescription(
            new NPAgentServerID(UUID.fromString("a753a5cb-e50d-4dcf-952c-27cb1898c66b")),
            "s2.example.com",
            50000,
            NPTLSDisabled.TLS_DISABLED,
            1_000_000
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("server-set-tls ");
    w.print(" --server a753a5cb-e50d-4dcf-952c-27cb1898c66b ");
    w.print(" --enabled false ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerGet.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerPut.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellServerSetTLS2()
    throws Exception
  {
    Mockito.when(this.consoleClient.execute(isA(NPACCommandServerGet.class)))
      .thenReturn(new NPACResponseServer(
        UUID.randomUUID(),
        UUID.randomUUID(),
        Optional.of(
          new NPAgentServerDescription(
            new NPAgentServerID(UUID.fromString("a753a5cb-e50d-4dcf-952c-27cb1898c66b")),
            "s2.example.com",
            50000,
            NPTLSDisabled.TLS_DISABLED,
            1_000_000
          )
        )
      ));

    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("server-set-tls ");
    w.print(" --server a753a5cb-e50d-4dcf-952c-27cb1898c66b ");
    w.print(" --enabled true ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(1, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandServerGet.class));
    Mockito.verify(this.consoleClient, new Times(0))
      .execute(isA(NPACCommandServerPut.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellAgentServerAssign0()
    throws Exception
  {
    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("agent-server-assign ");
    w.print(" --agent a ");
    w.print(" --server a753a5cb-e50d-4dcf-952c-27cb1898c66b ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandAgentServerAssign.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }

  @Test
  public void testShellAgentServerUnassign0()
    throws Exception
  {
    final var w = this.terminal.sendInputToTerminalWriter();
    w.println("set --terminate-on-errors true");
    w.print("agent-server-unassign ");
    w.print(" --agent a ");
    w.println();
    w.flush();
    w.close();

    this.waitForShell();
    assertEquals(0, this.exitCode);

    Mockito.verify(this.consoleClient, new Times(1))
      .execute(isA(NPACCommandAgentServerAssign.class));
    Mockito.verify(this.consoleClient, new Times(1))
      .close();
  }
}
