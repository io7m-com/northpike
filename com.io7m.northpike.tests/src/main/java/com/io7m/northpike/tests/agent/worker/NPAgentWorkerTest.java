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


package com.io7m.northpike.tests.agent.worker;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseConfiguration;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseCreate;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerAssignType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentWorkExecPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUpgrade;
import com.io7m.northpike.agent.database.sqlite.NPASDatabases;
import com.io7m.northpike.agent.internal.events.NPAgentUpdated;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerConnectionStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerConnectionStopped;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerExecutorStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerExecutorStopped;
import com.io7m.northpike.agent.internal.worker.NPAgentWorker;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.agent.workexec.local.NPWorkExecutorsLocal;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventService;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tls.NPTLSContextService;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.time.Clock;
import java.util.Locale;
import java.util.Optional;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPAgentWorkerTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentWorkerTest.class);

  private RPServiceDirectory services;
  private NPAgentLocalName name;
  private NPEventInterceptingService events;
  private NPStrings strings;
  private NPAgentDatabaseType database;
  private NPAgentKeyPairFactoryEd448 keys;

  @BeforeEach
  public void setup(
    final @TempDir Path directory)
    throws Exception
  {
    this.services =
      new RPServiceDirectory();
    this.keys =
      new NPAgentKeyPairFactoryEd448();
    this.name =
      NPAgentLocalName.of("a");

    this.events =
      new NPEventInterceptingService(
        NPEventService.create(NPTelemetryNoOp.noop())
      );
    this.strings =
      NPStrings.create(Locale.ROOT);

    final var databaseConfig =
      new NPAgentDatabaseConfiguration(
        "SQLITE",
        directory.resolve("agent.db"),
        NPAgentDatabaseCreate.CREATE_DATABASE,
        NPAgentDatabaseUpgrade.UPGRADE_DATABASE
      );

    this.database =
      new NPASDatabases()
        .open(new NPAgentDatabaseSetup(
          databaseConfig,
          NPTelemetryNoOp.noop(),
          Clock.systemUTC(),
          this.strings
        ), status -> LOG.debug("Database: {}", status));

    this.services.register(
      NPTLSContextServiceType.class,
      NPTLSContextService.create(NPTelemetryNoOp.noop()));
    this.services.register(
      NPStrings.class, this.strings);
    this.services.register(
      NPEventServiceType.class, this.events);
    this.services.register(
      NPAgentDatabaseType.class, this.database);
    this.services.register(
      NPAWorkExecutorFactoryType.class,
      new NPWorkExecutorsLocal()
    );
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.services.close();
  }

  /**
   * A worker with no configuration does nothing.
   *
   * @throws Exception On errors
   */

  @Test
  public void testWorkerNoConfiguration()
    throws Exception
  {
    try (var s = NPAgentWorker.create(this.services, this.name)) {
      Thread.sleep(1_000L);
    }
  }

  /**
   * An existing worker is started, but no server connection is created.
   *
   * @throws Exception On errors
   */

  @Test
  public void testWorkerNoConnection()
    throws Exception
  {
    try (var c = this.database.openConnection()) {
      try (var t = c.openTransaction()) {
        t.queries(AgentPutType.class)
          .execute(new NPAgentLocalDescription(
            NPAgentLocalName.of("a"),
            this.keys.generateKeyPair()
          ));
        t.commit();
      }
    }

    try (var s = NPAgentWorker.create(this.services, this.name)) {
      Thread.sleep(1_000L);
    }

    this.dumpEvents();
  }

  /**
   * An existing worker is started and a server connection is created. No
   * work executor is defined, so no work controller task is created.
   *
   * @throws Exception On errors
   */

  @Test
  public void testWorkerConnection()
    throws Exception
  {
    try (var c = this.database.openConnection()) {
      try (var t = c.openTransaction()) {
        t.queries(AgentPutType.class)
          .execute(new NPAgentLocalDescription(
            NPAgentLocalName.of("a"),
            this.keys.generateKeyPair()
          ));
        final var serverId = new NPAgentServerID(UUID.randomUUID());
        t.queries(ServerPutType.class)
          .execute(new NPAgentServerDescription(
            serverId,
            "localhost",
            50000,
            NPTLSDisabled.TLS_DISABLED,
            1_000_000
          ));
        t.queries(AgentServerAssignType.class)
          .execute(new AgentServerAssignType.Parameters(
            NPAgentLocalName.of("a"),
            serverId
          ));
        t.commit();
      }
    }

    try (var s = NPAgentWorker.create(this.services, this.name)) {
      Thread.sleep(1_000L);
    }

    this.dumpEvents();
    assertEquals(connectionStarted("a"), this.takeEvent());
  }

  /**
   * An existing worker is started and a server connection is created. A
   * work executor is defined, so a work controller task is created.
   *
   * Unsetting the work executor shuts down the work controller.
   *
   * @throws Exception On errors
   */

  @Test
  public void testWorkerController(
    final @TempDir Path directory)
    throws Exception
  {
    try (var c = this.database.openConnection()) {
      try (var t = c.openTransaction()) {
        t.queries(AgentPutType.class)
          .execute(new NPAgentLocalDescription(
            NPAgentLocalName.of("a"),
            this.keys.generateKeyPair()
          ));
        t.queries(AgentWorkExecPutType.class)
          .execute(new AgentWorkExecPutType.Parameters(
            NPAgentLocalName.of("a"),
            Optional.of(
              NPAWorkExecutorConfiguration.builder()
                .setExecutorType(NPAWorkExecName.of("workexec.local"))
                .setTemporaryDirectory(directory.resolve("tmp"))
                .setWorkDirectory(directory.resolve("work"))
                .build()
            )
          ));
        t.commit();
      }
    }

    try (var s = NPAgentWorker.create(this.services, this.name)) {
      Thread.sleep(1_000L);

      try (var c = this.database.openConnection()) {
        try (var t = c.openTransaction()) {
          t.queries(AgentWorkExecPutType.class)
            .execute(new AgentWorkExecPutType.Parameters(
              NPAgentLocalName.of("a"),
              Optional.empty()
            ));
          t.commit();
        }
      }

      this.events.emit(new NPAgentUpdated(NPAgentLocalName.of("a")));
      Thread.sleep(1_000L);
    }

    this.dumpEvents();
    assertEquals(executorStarted("a"), this.takeEvent());
    assertEquals(agentUpdated("a"), this.takeEvent());
    assertEquals(executorStopped("a"), this.takeEvent());
  }

  private static NPAgentUpdated agentUpdated(
    final String name)
  {
    return new NPAgentUpdated(NPAgentLocalName.of(name));
  }

  private static NPAgentWorkerConnectionStarted connectionStarted(
    final String name)
  {
    return new NPAgentWorkerConnectionStarted(NPAgentLocalName.of(name));
  }

  private static NPAgentWorkerConnectionStopped connectionStopped(
    final String name)
  {
    return new NPAgentWorkerConnectionStopped(NPAgentLocalName.of(name));
  }

  private static NPAgentWorkerExecutorStarted executorStarted(
    final String name)
  {
    return new NPAgentWorkerExecutorStarted(NPAgentLocalName.of(name));
  }

  private static NPAgentWorkerExecutorStopped executorStopped(
    final String name)
  {
    return new NPAgentWorkerExecutorStopped(NPAgentLocalName.of(name));
  }

  private NPEventType takeEvent()
  {
    return this.events.eventQueue().remove();
  }


  private void dumpEvents()
  {
    for (final var e : this.events.eventQueue()) {
      LOG.debug("{}", e);
    }
  }
}
