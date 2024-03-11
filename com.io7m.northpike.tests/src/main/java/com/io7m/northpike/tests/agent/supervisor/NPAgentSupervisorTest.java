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


package com.io7m.northpike.tests.agent.supervisor;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseConfiguration;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseCreate;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseSetup;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUpgrade;
import com.io7m.northpike.agent.database.sqlite.NPASDatabases;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerStopped;
import com.io7m.northpike.agent.internal.supervisor.NPAgentSupervisor;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
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
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPAgentSupervisorTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentSupervisorTest.class);

  private RPServiceDirectory services;
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
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.services.close();
  }

  /**
   * A supervisor with no configuration does nothing.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSupervisorNoConfiguration()
    throws Exception
  {
    try (var s = NPAgentSupervisor.create(this.services)) {
      Thread.sleep(1_000L);
    }

    assertEquals(List.of(), this.events.eventQueue().stream().toList());
  }

  /**
   * Three existing workers are started.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSupervisor3()
    throws Exception
  {
    try (var c = this.database.openConnection()) {
      try (var t = c.openTransaction()) {
        t.queries(NPAgentDatabaseQueriesAgentsType.AgentPutType.class)
          .execute(new NPAgentLocalDescription(
            NPAgentLocalName.of("a"),
            this.keys.generateKeyPair()
          ));
        t.queries(NPAgentDatabaseQueriesAgentsType.AgentPutType.class)
          .execute(new NPAgentLocalDescription(
            NPAgentLocalName.of("b"),
            this.keys.generateKeyPair()
          ));
        t.queries(NPAgentDatabaseQueriesAgentsType.AgentPutType.class)
          .execute(new NPAgentLocalDescription(
            NPAgentLocalName.of("c"),
            this.keys.generateKeyPair()
          ));
        t.commit();
      }
    }

    try (var s = NPAgentSupervisor.create(this.services)) {
      Thread.sleep(1_000L);
    }

    this.dumpEvents();
    assertEquals(workerStarted("a"), this.takeEvent());
    assertEquals(workerStarted("b"), this.takeEvent());
    assertEquals(workerStarted("c"), this.takeEvent());
    assertEquals(workerStopped("a"), this.takeEvent());
    assertEquals(workerStopped("b"), this.takeEvent());
    assertEquals(workerStopped("c"), this.takeEvent());
  }

  private static NPAgentWorkerStopped workerStopped(
    final String name)
  {
    return new NPAgentWorkerStopped(NPAgentLocalName.of(name));
  }

  private static NPAgentWorkerStarted workerStarted(
    final String name)
  {
    return new NPAgentWorkerStarted(NPAgentLocalName.of(name));
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
