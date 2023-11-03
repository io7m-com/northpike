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

package com.io7m.northpike.tests.agent.database;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseConfiguration;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseConnectionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseCreate;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentDeleteType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerAssignType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerUnassignType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerDeleteType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerListType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerListType.Parameters;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseTransactionType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUpgrade;
import com.io7m.northpike.agent.database.sqlite.NPASDatabases;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabled;
import com.io7m.northpike.model.tls.NPTLSStoreConfiguration;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Clock;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Locale;
import java.util.Optional;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPAgentDatabaseTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentDatabaseTest.class);

  private NPASDatabases databases;
  private NPAgentDatabaseType database;
  private NPAgentDatabaseConnectionType connection;
  private NPAgentDatabaseTransactionType transaction;
  private Path databaseFile;

  @BeforeEach
  public void setup(
    final @TempDir Path directory)
    throws Exception
  {
    this.databaseFile =
      directory.resolve("agent.db");

    this.databases = new NPASDatabases();
    this.database =
      this.databases.open(
        new NPAgentDatabaseSetup(
          new NPAgentDatabaseConfiguration(
            "SQLITE",
            this.databaseFile,
            NPAgentDatabaseCreate.CREATE_DATABASE,
            NPAgentDatabaseUpgrade.UPGRADE_DATABASE
          ),
          NPTelemetryNoOp.noop(),
          Clock.systemUTC(),
          NPStrings.create(Locale.getDefault())
        ),
        s -> LOG.debug("{}", s)
      );

    this.connection = this.database.openConnection();
    this.transaction = this.connection.openTransaction();
  }

  @AfterEach
  public void tearDown()
    throws NPAgentDatabaseException
  {
    this.transaction.close();
    this.connection.close();
    this.database.close();
  }

  @Test
  public void testAgentPutGet()
    throws Exception
  {
    final var agentPut =
      this.transaction.queries(AgentPutType.class);
    final var agentGet =
      this.transaction.queries(AgentGetType.class);
    final var agentDelete =
      this.transaction.queries(AgentDeleteType.class);

    final var x =
      new NPAgentLocalDescription(
        NPAgentLocalName.of("x"),
        new NPAgentKeyPairFactoryEd448().generateKeyPair()
      );

    final var y =
      new NPAgentLocalDescription(
        NPAgentLocalName.of("y"),
        new NPAgentKeyPairFactoryEd448().generateKeyPair()
      );

    agentPut.execute(x);
    agentPut.execute(y);

    assertEquals(x, agentGet.execute(x.name()).orElseThrow());
    assertEquals(y, agentGet.execute(y.name()).orElseThrow());

    agentDelete.execute(x.name());
    assertEquals(Optional.empty(), agentGet.execute(x.name()));
    assertEquals(y, agentGet.execute(y.name()).orElseThrow());

    agentDelete.execute(y.name());
    assertEquals(Optional.empty(), agentGet.execute(x.name()));
    assertEquals(Optional.empty(), agentGet.execute(y.name()));
  }

  @Test
  public void testServerPutGet()
    throws Exception
  {
    final var serverPut =
      this.transaction.queries(ServerPutType.class);
    final var serverGet =
      this.transaction.queries(ServerGetType.class);

    final var x =
      new NPAgentServerDescription(
        new NPAgentServerID(UUID.randomUUID()),
        "example.com",
        4000,
        NPTLSDisabled.TLS_DISABLED,
        1_000_000
      );

    final var y =
      new NPAgentServerDescription(
        new NPAgentServerID(UUID.randomUUID()),
        "example.com",
        5000,
        NPTLSDisabled.TLS_DISABLED,
        1_000_000
      );

    serverPut.execute(x);
    serverPut.execute(y);

    assertEquals(x, serverGet.execute(x.id()).orElseThrow());
    assertEquals(y, serverGet.execute(y.id()).orElseThrow());
  }

  @Test
  public void testServerAssign()
    throws Exception
  {
    final var agentPut =
      this.transaction.queries(AgentPutType.class);
    final var serverPut =
      this.transaction.queries(ServerPutType.class);
    final var serverDelete =
      this.transaction.queries(ServerDeleteType.class);
    final var agentServerGet =
      this.transaction.queries(AgentServerGetType.class);
    final var agentServerAssign =
      this.transaction.queries(AgentServerAssignType.class);
    final var agentServerUnassign =
      this.transaction.queries(AgentServerUnassignType.class);

    final var ax =
      new NPAgentLocalDescription(
        NPAgentLocalName.of("x"),
        new NPAgentKeyPairFactoryEd448().generateKeyPair()
      );

    final var ay =
      new NPAgentLocalDescription(
        NPAgentLocalName.of("y"),
        new NPAgentKeyPairFactoryEd448().generateKeyPair()
      );

    final var sx =
      new NPAgentServerDescription(
        new NPAgentServerID(UUID.randomUUID()),
        "example.com",
        4000,
        NPTLSDisabled.TLS_DISABLED,
        1_000_000
      );

    final var sy =
      new NPAgentServerDescription(
        new NPAgentServerID(UUID.randomUUID()),
        "example.com",
        5000,
        NPTLSDisabled.TLS_DISABLED,
        1_000_000
      );

    agentPut.execute(ax);
    agentPut.execute(ay);
    serverPut.execute(sx);
    serverPut.execute(sy);

    assertEquals(Optional.empty(), agentServerGet.execute(ax.name()));
    agentServerAssign.execute(
      new AgentServerAssignType.Parameters(ax.name(), sx.id())
    );
    assertEquals(sx.id(), agentServerGet.execute(ax.name()).orElseThrow());
    agentServerUnassign.execute(ax.name());
    assertEquals(Optional.empty(), agentServerGet.execute(ax.name()));
    agentServerAssign.execute(
      new AgentServerAssignType.Parameters(ax.name(), sx.id())
    );
    assertEquals(sx.id(), agentServerGet.execute(ax.name()).orElseThrow());
    serverDelete.execute(sx.id());
    assertEquals(Optional.empty(), agentServerGet.execute(ax.name()));
  }

  @Test
  public void testServerList()
    throws Exception
  {
    final var serverPut =
      this.transaction.queries(ServerPutType.class);
    final var serverList =
      this.transaction.queries(ServerListType.class);

    final var servers = new ArrayList<NPAgentServerDescription>();
    for (int index = 1; index <= 1000; ++index) {
      servers.add(
        new NPAgentServerDescription(
          new NPAgentServerID(UUID.randomUUID()),
          "h%d.example.com".formatted(Integer.valueOf(index)),
          index,
          new NPTLSEnabled(
            new NPTLSStoreConfiguration(
              "CANONMILL",
              "CANONMILL",
              "change",
              Paths.get("/tmp")
            ),
            new NPTLSStoreConfiguration(
              "CANONMILL",
              "CANONMILL",
              "change",
              Paths.get("/tmp")
            )
          ),
          1_000_000
        )
      );
    }

    servers.sort(Comparator.comparing(o -> o.id().value()));

    for (final var s : servers) {
      serverPut.execute(s);
    }

    final var start =
      serverList.execute(new Parameters(Optional.empty(), 10L));

    final var summaries = new ArrayList<>(start);
    var last = start.getLast();
    while (true) {
      final var next =
        serverList.execute(new Parameters(Optional.of(last.id()), 10L));

      if (next.isEmpty()) {
        break;
      }
      summaries.addAll(next);
      last = next.getLast();
    }

    summaries.sort(Comparator.comparing(o -> o.id().value()));

    assertEquals(
      summaries,
      servers.stream()
        .map(NPAgentServerDescription::summary)
        .toList()
    );
  }
}
