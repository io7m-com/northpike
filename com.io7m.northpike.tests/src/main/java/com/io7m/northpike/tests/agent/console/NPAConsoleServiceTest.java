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


package com.io7m.northpike.tests.agent.console;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.api.NPAgentConsoleConfiguration;
import com.io7m.northpike.agent.console_client.NPAConsoleClients;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientConfiguration;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseConfiguration;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseCreate;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUpgrade;
import com.io7m.northpike.agent.database.sqlite.NPASDatabases;
import com.io7m.northpike.agent.internal.console.NPAConsoleService;
import com.io7m.northpike.agent.internal.console.NPAConsoleServiceType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentCreate;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentDelete;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentList;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentServerAssign;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerDelete;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerList;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecPut;
import com.io7m.northpike.server.internal.events.NPEventService;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Clock;
import java.util.Locale;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import static java.util.UUID.randomUUID;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

@Timeout(value = 5L, unit = TimeUnit.SECONDS)
public final class NPAConsoleServiceTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAConsoleServiceTest.class);

  private RPServiceDirectory services;
  private NPAgentConsoleConfiguration configuration;
  private NPAConsoleServiceType console;
  private NPAConsoleClients clients;
  private NPStrings strings;
  private NPAConsoleClientType client;
  private InetSocketAddress address;
  private NPAgentDatabaseType database;
  private NPEventInterceptingService events;

  @BeforeEach
  public void setup(
    final @TempDir Path directory)
    throws Exception
  {
    this.strings = NPStrings.create(Locale.ROOT);

    final var databaseFile =
      directory.resolve("agent.db");

    final var dbConfiguration =
      new NPAgentDatabaseConfiguration(
        "SQLITE",
        databaseFile,
        NPAgentDatabaseCreate.CREATE_DATABASE,
        NPAgentDatabaseUpgrade.UPGRADE_DATABASE
      );

    this.database =
      new NPASDatabases()
        .open(
          new NPAgentDatabaseSetup(
            dbConfiguration,
            NPTelemetryNoOp.noop(),
            Clock.systemUTC(),
            this.strings
          ),
          status -> LOG.debug("Database: {}", status)
        );

    this.events =
      new NPEventInterceptingService(
        NPEventService.create(NPTelemetryNoOp.noop())
      );

    this.services = new RPServiceDirectory();
    this.services.register(NPStrings.class, this.strings);
    this.services.register(NPAgentDatabaseType.class, this.database);
    this.services.register(NPEventServiceType.class, this.events);
    this.services.register(
      NPTelemetryServiceType.class,
      NPTelemetryNoOp.noop());

    this.address =
      new InetSocketAddress(
        InetAddress.getLoopbackAddress(),
        45000
      );

    this.configuration =
      new NPAgentConsoleConfiguration(
        this.address.getAddress(),
        this.address.getPort(),
        "access"
      );

    this.console = NPAConsoleService.create(this.services, this.configuration);
    this.services.register(NPAConsoleServiceType.class, this.console);
    this.console.start();

    this.clients =
      new NPAConsoleClients();
    this.client =
      this.clients.createConsoleClient(
        new NPAConsoleClientConfiguration(this.strings)
      );
    this.services.register(NPAConsoleClientType.class, this.client);
  }

  @AfterEach
  public void tearDown()
  {
    try {
      this.services.close();
    } catch (final IOException e) {
      // Not a problem
    }
  }

  @Test
  public void testLoginDisconnect()
    throws Exception
  {
    this.client.login(this.address, "access");
    Thread.sleep(1_000L);
  }

  @Test
  public void testAgentCreateListDelete()
    throws Exception
  {
    this.client.login(this.address, "access");

    final var name = NPAgentLocalName.of("a");
    this.client.execute(
      new NPACCommandAgentCreate(randomUUID(), name)
    );

    final var get0 =
      this.client.execute(new NPACCommandAgentGet(randomUUID(), name));

    assertEquals(name, get0.results().orElseThrow().name());

    final var list =
      this.client.execute(
        new NPACCommandAgentList(randomUUID(), Optional.empty(), 10L)
      );

    assertEquals(name, list.results().get(0));

    this.client.execute(new NPACCommandAgentDelete(randomUUID(), name));

    final var get1 =
      this.client.execute(new NPACCommandAgentGet(randomUUID(), name));

    assertEquals(Optional.empty(), get1.results());
  }

  @Test
  public void testServerCreateListDelete()
    throws Exception
  {
    this.client.login(this.address, "access");

    final var name = new NPAgentServerID(randomUUID());

    this.client.execute(
      new NPACCommandServerPut(
        randomUUID(),
        new NPAgentServerDescription(
          name,
          "s1.example.com",
          41000,
          NPTLSDisabled.TLS_DISABLED,
          1_000_000
        )
      )
    );

    final var get0 =
      this.client.execute(new NPACCommandServerGet(randomUUID(), name));

    assertEquals(name, get0.results().orElseThrow().id());

    final var list =
      this.client.execute(
        new NPACCommandServerList(randomUUID(), Optional.empty(), 10L)
      );

    assertEquals(name, list.results().get(0).id());

    this.client.execute(new NPACCommandServerDelete(randomUUID(), name));

    final var get1 =
      this.client.execute(new NPACCommandServerGet(randomUUID(), name));

    assertEquals(Optional.empty(), get1.results());
  }

  @Test
  public void testAgentCreateWorkExec()
    throws Exception
  {
    this.client.login(this.address, "access");

    final var name = NPAgentLocalName.of("a");
    this.client.execute(
      new NPACCommandAgentCreate(randomUUID(), name)
    );

    final var workExec =
      NPAWorkExecutorConfiguration.builder()
        .setWorkDirectory(Paths.get("a"))
        .setTemporaryDirectory(Paths.get("b"))
        .setExecutorType(new RDottedName("t"))
        .build();

    this.client.execute(new NPACCommandWorkExecPut(
      randomUUID(),
      name,
      Optional.of(workExec)
    ));

    {
      final var r =
        this.client.execute(new NPACCommandWorkExecGet(randomUUID(), name));

      assertEquals(Optional.of(workExec), r.results());
    }

    this.client.execute(new NPACCommandWorkExecPut(
      randomUUID(),
      name,
      Optional.empty()
    ));

    {
      final var r =
        this.client.execute(new NPACCommandWorkExecGet(randomUUID(), name));

      assertEquals(Optional.empty(), r.results());
    }
  }

  @Test
  public void testAgentServerAssignNonexistent()
    throws Exception
  {
    this.client.login(this.address, "access");

    final var name = NPAgentLocalName.of("a");
    this.client.execute(
      new NPACCommandAgentCreate(randomUUID(), name)
    );

    final var ex =
      assertThrows(NPException.class, () -> {
        this.client.execute(new NPACCommandAgentServerAssign(
          randomUUID(),
          name,
          Optional.of(new NPAgentServerID(randomUUID()))
        ));
      });

    assertEquals(NPStandardErrorCodes.errorSqlForeignKey(), ex.errorCode());
  }
}
