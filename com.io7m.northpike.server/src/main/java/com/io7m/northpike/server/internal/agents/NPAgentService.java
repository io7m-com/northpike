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


package com.io7m.northpike.server.internal.agents;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.CloseableTrackerType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.NPServerSocketServiceType;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main agent service.
 */

public final class NPAgentService implements NPAgentServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentService.class);

  private final CloseableCollectionType<NPServerException> resources;
  private final NPStrings strings;
  private final NPServerConfiguration configuration;
  private final NPClockServiceType clock;
  private final NPEventServiceType events;
  private final NPTelemetryServiceType telemetry;
  private final NPMetricsServiceType metrics;
  private final NPDatabaseType database;
  private final NPServerSocketServiceType sockets;
  private final ExecutorService agentExecutor;
  private final AtomicBoolean closed;
  private final ExecutorService mainExecutor;
  private final CompletableFuture<Void> future;
  private final CloseableTrackerType<NPServerException> tasks;
  private ServerSocket socket;

  private NPAgentService(
    final CloseableCollectionType<NPServerException> inResources,
    final CloseableTrackerType<NPServerException> inTasks,
    final NPStrings inStrings,
    final NPServerConfiguration inConfiguration,
    final NPClockServiceType inClock,
    final NPEventServiceType inEvents,
    final NPTelemetryServiceType inTelemetry,
    final NPMetricsServiceType inMetrics,
    final NPDatabaseType inDatabase,
    final NPServerSocketServiceType inSockets,
    final ExecutorService inMainExecutor,
    final ExecutorService inAgentExecutor)
  {
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.tasks =
      Objects.requireNonNull(inTasks, "inTasks");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.metrics =
      Objects.requireNonNull(inMetrics, "metrics");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.sockets =
      Objects.requireNonNull(inSockets, "sockets");
    this.agentExecutor =
      Objects.requireNonNull(inAgentExecutor, "agentExecutor");
    this.mainExecutor =
      Objects.requireNonNull(inMainExecutor, "inMainExecutor");
    this.closed =
      new AtomicBoolean(true);
    this.future =
      new CompletableFuture<>();
  }

  /**
   * Create an agent service.
   *
   * @param services The service directory
   *
   * @return The service
   */

  public static NPAgentServiceType create(
    final RPServiceDirectoryType services)
  {
    Objects.requireNonNull(services, "services");

    final var configuration =
      services.requireService(NPConfigurationServiceType.class);
    final var events =
      services.requireService(NPEventServiceType.class);
    final var strings =
      services.requireService(NPStrings.class);
    final var telemetry =
      services.requireService(NPTelemetryServiceType.class);
    final var database =
      services.requireService(NPDatabaseType.class);
    final var clock =
      services.requireService(NPClockServiceType.class);
    final var sockets =
      services.requireService(NPServerSocketServiceType.class);
    final var metrics =
      services.requireService(NPMetricsServiceType.class);

    final var resources =
      NPServerResources.createResources();
    final var tracker =
      NPServerResources.createTracker();

    resources.add(tracker);

    final var mainExecutor =
      Executors.newSingleThreadExecutor(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.server.agent.service[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    resources.add(mainExecutor::shutdown);

    final var agentExecutor =
      Executors.newCachedThreadPool(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.server.agent[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    resources.add(agentExecutor::shutdown);

    return new NPAgentService(
      resources,
      tracker,
      strings,
      configuration.configuration(),
      clock,
      events,
      telemetry,
      metrics,
      database,
      sockets,
      mainExecutor,
      agentExecutor
    );
  }

  private static void pauseBriefly()
  {
    try {
      Thread.sleep(500L);
    } catch (final InterruptedException ex) {
      Thread.currentThread().interrupt();
    }
  }

  @Override
  public CompletableFuture<Void> start()
  {
    if (this.closed.compareAndSet(true, false)) {
      this.mainExecutor.execute(this::run);
    }
    return this.future;
  }

  private void run()
  {
    LOG.info(
      "Starting Agent service on {}:{}",
      this.configuration.agentConfiguration().localAddress(),
      Integer.valueOf(this.configuration.agentConfiguration().localPort())
    );

    this.metrics.setAgentsConnected(0);

    while (!this.closed.get()) {

      /*
       * Try to bind a listening socket. Repeat until the socket either
       * opens or someone shuts the server down.
       */

      try {
        this.socket = this.openSocket();
      } catch (final IOException e) {
        LOG.error("Bind: ", e);
        pauseBriefly();
        continue;
      }

      this.events.emit(new NPAgentServiceStarted());
      this.future.complete(null);

      /*
       * Repeatedly accept clients from the bound socket.
       */

      while (!this.closed.get()) {
        final Socket newSocket;
        try {
          newSocket = this.socket.accept();
          this.events.emit(new NPAgentConnected(
            newSocket.getInetAddress(),
            newSocket.getPort()
          ));
        } catch (final Exception e) {
          LOG.error("Accept: ", e);
          continue;
        }

        this.agentExecutor.execute(() -> this.createAndRunAgentTask(newSocket));
      }
    }
  }

  private void createAndRunAgentTask(
    final Socket clientSocket)
  {
    final NPAgentTask task;
    try {
      task = new NPAgentTask(
        this.strings,
        this.telemetry,
        this.clock,
        this.database,
        this.events,
        this.configuration.agentConfiguration(),
        clientSocket
      );
    } catch (final Exception e) {
      LOG.debug("Agent Creation: ", e);
      try {
        clientSocket.close();
      } catch (final IOException ex) {
        LOG.debug("Close: ", ex);
      }
      return;
    }

    this.tasks.add(task);
    this.metrics.setAgentsConnected(this.tasks.size());

    try (task) {
      task.run();
    } catch (final Exception e) {
      LOG.debug("Agent: ", e);
    }
  }

  private ServerSocket openSocket()
    throws IOException
  {
    final var c =
      this.configuration.agentConfiguration();

    final var newSocket =
      c.useTLS()
        ? this.sockets.createTLSSocket()
        : this.sockets.createPlainSocket();

    try {
      newSocket.setReuseAddress(true);
      newSocket.setPerformancePreferences(1, 2, 0);
      newSocket.bind(new InetSocketAddress(c.localAddress(), c.localPort()));
    } catch (final IOException e) {
      newSocket.close();
      throw e;
    }

    return this.resources.add(newSocket);
  }

  @Override
  public String description()
  {
    return "The agent service.";
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
      this.future.complete(null);
    }
  }

  @Override
  public String toString()
  {
    return "[NPAgentService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
