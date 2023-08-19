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


package com.io7m.northpike.tests.server.agents;

import com.io7m.northpike.agent.NPAgents;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentStatus;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseFactoryType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.server.internal.agents.NPAgentServerSocketServiceType;
import com.io7m.northpike.server.internal.agents.NPAgentService;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.clock.NPClock;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.events.NPEventService;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.server.internal.telemetry.NPTelemetryNoOp;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.mockito.Mockito;
import org.mockito.internal.verification.AtLeast;

import javax.net.ServerSocketFactory;
import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.time.Clock;
import java.util.HashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTED;
import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTION_FAILED;
import static com.io7m.northpike.tests.server.NPServerConfigurations.createFakeServerConfiguration;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;

public final class NPAgentServiceTest
{
  private RPServiceDirectory services;
  private NPAgentServiceType service;
  private NPClockServiceType clock;
  private NPConfigurationServiceType configuration;
  private NPStrings strings;
  private NPTelemetryNoOp telemetry;
  private NPDatabaseType database;
  private NPDatabaseFactoryType databases;
  private NPAgents agents;
  private NPKey agentKey0;
  private NPKey agentKey1;
  private NPAgentConfiguration agentConfiguration0;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPDatabaseQueriesAgentsType.GetType agentGet;
  private NPDatabaseQueriesAgentsType.GetByKeyType agentGetByKey;
  private NPDatabaseQueriesAgentsType.PutType agentPut;
  private HashSet<NPAgentStatus> agentEvents;
  private NPAgentDescription agent0;
  private NPAgentServerSocketServiceType sockets;
  private NPEventServiceType events;
  private NPMetricsServiceType metrics;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.services =
      new RPServiceDirectory();
    this.clock =
      new NPClock(Clock.systemUTC());
    this.configuration =
      Mockito.mock(NPConfigurationServiceType.class);
    this.strings =
      NPStrings.create(Locale.ROOT);
    this.telemetry =
      NPTelemetryNoOp.noop();
    this.database =
      Mockito.mock(NPDatabaseType.class);
    this.databases =
      Mockito.mock(NPDatabaseFactoryType.class);
    this.connection =
      Mockito.mock(NPDatabaseConnectionType.class);
    this.transaction =
      Mockito.mock(NPDatabaseTransactionType.class);
    this.sockets =
      Mockito.mock(NPAgentServerSocketServiceType.class);
    this.events =
      NPEventService.create(NPTelemetryNoOp.noop());
    this.metrics =
      Mockito.mock(NPMetricsServiceType.class);

    Mockito.when(this.database.openConnection(any()))
      .thenReturn(this.connection);
    Mockito.when(this.connection.openTransaction())
      .thenReturn(this.transaction);

    this.agentPut =
      Mockito.mock(NPDatabaseQueriesAgentsType.PutType.class);
    this.agentGet =
      Mockito.mock(NPDatabaseQueriesAgentsType.GetType.class);
    this.agentGetByKey =
      Mockito.mock(NPDatabaseQueriesAgentsType.GetByKeyType.class);

    Mockito.when(this.transaction.queries(NPDatabaseQueriesAgentsType.GetType.class))
      .thenReturn(this.agentGet);
    Mockito.when(this.transaction.queries(NPDatabaseQueriesAgentsType.GetByKeyType.class))
      .thenReturn(this.agentGetByKey);
    Mockito.when(this.transaction.queries(NPDatabaseQueriesAgentsType.PutType.class))
      .thenReturn(this.agentPut);

    this.services.register(
      NPClockServiceType.class, this.clock);
    this.services.register(
      NPConfigurationServiceType.class, this.configuration);
    this.services.register(
      NPStrings.class, this.strings);
    this.services.register(
      NPTelemetryServiceType.class, this.telemetry);
    this.services.register(
      NPDatabaseType.class, this.database);
    this.services.register(
      NPAgentServerSocketServiceType.class, this.sockets);
    this.services.register(
      NPEventServiceType.class, this.events);
    this.services.register(
      NPMetricsServiceType.class, this.metrics);

    Mockito.when(this.configuration.configuration())
      .thenReturn(createFakeServerConfiguration(this.strings, this.databases));

    this.service =
      NPAgentService.create(this.services);

    this.agents =
      new NPAgents();
    this.agentEvents =
      new HashSet<>();
    this.agentKey0 =
      NPKey.generate();
    this.agentKey1 =
      NPKey.generate();

    this.agent0 =
      new NPAgentDescription(
        NPAgentID.of("ab3bdd26-7d7b-5c05-b0aa-f0717b6dbcef"),
        "Agent 0",
        this.agentKey0,
        Map.of(),
        Map.of(),
        Map.of()
      );

    this.agentConfiguration0 =
      new NPAgentConfiguration(
        this.strings,
        InetAddress.getLocalHost(),
        20048,
        false,
        this.agentKey0,
        1000000
      );
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.service.close();
  }

  /**
   * Authentication fails for undefined agents.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 5L, unit = TimeUnit.SECONDS)
  public void testAuthenticationFails()
    throws Exception
  {
    Mockito.when(this.sockets.createSocket())
      .thenReturn(ServerSocketFactory.getDefault().createServerSocket());

    this.service.start().get(5L, TimeUnit.SECONDS);

    Mockito.when(this.agentGetByKey.execute(any()))
      .thenReturn(Optional.empty());

    try (var agent = this.agents.createAgent(this.agentConfiguration0)) {
      agent.status()
        .subscribe((oldValue, newValue) -> this.agentEvents.add(newValue));
      agent.start();

      Thread.sleep(1000L);
      this.assertConnectionStatus(CONNECTION_FAILED);
    }
  }

  /**
   * Authentication succeeds for agents.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 5L, unit = TimeUnit.SECONDS)
  public void testAuthenticationSucceeds()
    throws Exception
  {
    Mockito.when(this.sockets.createSocket())
      .thenReturn(ServerSocketFactory.getDefault().createServerSocket());

    this.service.start().get(5L, TimeUnit.SECONDS);

    Mockito.when(this.agentGetByKey.execute(any()))
      .thenReturn(Optional.of(this.agent0));
    Mockito.when(this.agentGet.execute(any()))
      .thenReturn(Optional.of(this.agent0));

    try (var agent = this.agents.createAgent(this.agentConfiguration0)) {
      agent.status()
        .subscribe((oldValue, newValue) -> this.agentEvents.add(newValue));
      agent.start();

      Thread.sleep(3L * 1000L);
      this.assertConnectionStatus(CONNECTED);
    }
  }

  /**
   * Binding a socket is re-attempted repeatedly.
   *
   * @throws Exception On errors
   */

  @Test
  @Timeout(value = 5L, unit = TimeUnit.SECONDS)
  public void testBindRepeated()
    throws Exception
  {
    final var socket =
      Mockito.mock(ServerSocket.class);
    Mockito.when(this.sockets.createSocket())
      .thenReturn(socket);

    Mockito.doThrow(new IOException())
      .when(socket)
      .bind(any());

    assertThrows(TimeoutException.class, () -> {
      this.service.start().get(3L, TimeUnit.SECONDS);
    });

    Mockito.verify(socket, new AtLeast(3))
      .bind(any());
  }

  private void assertConnectionStatus(
    final NPAgentStatus status)
  {
    assertTrue(
      this.agentEvents.contains(status),
      String.format("%s must contain %s", this.agentEvents, status)
    );
  }
}
