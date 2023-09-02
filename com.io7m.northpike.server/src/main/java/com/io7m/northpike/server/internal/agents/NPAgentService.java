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
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPAgentWorkItem;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashSet;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main agent service.
 */

public final class NPAgentService implements NPAgentServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentService.class);

  private final RPServiceDirectoryType services;
  private final CloseableCollectionType<NPServerException> resources;
  private final NPServerConfiguration configuration;
  private final NPEventServiceType events;
  private final NPMetricsServiceType metrics;
  private final NPAgentServerSocketServiceType sockets;
  private final ExecutorService agentExecutor;
  private final AtomicBoolean closed;
  private final ExecutorService mainExecutor;
  private final ScheduledExecutorService agentTicker;
  private final CompletableFuture<Void> future;
  private final ConcurrentHashMap.KeySetView<NPAgentTask, Boolean> agentTasks;
  private ServerSocket socket;

  private NPAgentService(
    final RPServiceDirectoryType inServices,
    final CloseableCollectionType<NPServerException> inResources,
    final NPServerConfiguration inConfiguration,
    final NPEventServiceType inEvents,
    final NPMetricsServiceType inMetrics,
    final NPAgentServerSocketServiceType inSockets,
    final ExecutorService inMainExecutor,
    final ExecutorService inAgentExecutor,
    final ScheduledExecutorService inAgentTicker)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.metrics =
      Objects.requireNonNull(inMetrics, "metrics");
    this.sockets =
      Objects.requireNonNull(inSockets, "sockets");
    this.agentExecutor =
      Objects.requireNonNull(inAgentExecutor, "agentExecutor");
    this.mainExecutor =
      Objects.requireNonNull(inMainExecutor, "inMainExecutor");
    this.agentTicker =
      Objects.requireNonNull(inAgentTicker, "agentTicker");
    this.closed =
      new AtomicBoolean(true);
    this.future =
      new CompletableFuture<>();
    this.agentTasks =
      ConcurrentHashMap.newKeySet();
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
    final var sockets =
      services.requireService(NPAgentServerSocketServiceType.class);
    final var metrics =
      services.requireService(NPMetricsServiceType.class);

    final var resources =
      NPServerResources.createResources();

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

    final var agentTicker =
      Executors.newSingleThreadScheduledExecutor(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.northpike.agent.periodic[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        thread.setDaemon(true);
        return thread;
      });

    resources.add(agentTicker::shutdown);

    return new NPAgentService(
      services,
      resources,
      configuration.configuration(),
      events,
      metrics,
      sockets,
      mainExecutor,
      agentExecutor,
      agentTicker
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

  @Override
  public NPSuitableAgents findSuitableAgentsFor(
    final NPAgentLabelMatchType require,
    final NPAgentLabelMatchType prefer)
  {
    Objects.requireNonNull(require, "require");
    Objects.requireNonNull(prefer, "prefer");

    final var available =
      new HashSet<NPAgentID>();
    final var preferred =
      new HashSet<NPAgentID>();

    for (final var task : this.agentTasks) {
      if (task.matches(require)) {
        available.add(task.agentId());
        if (task.matches(prefer)) {
          preferred.add(task.agentId());
        }
      }
    }

    return new NPSuitableAgents(available, preferred);
  }

  @Override
  public boolean offerWorkItem(
    final NPAgentID agent,
    final NPAgentWorkItem workItem)
  {
    Objects.requireNonNull(agent, "agent");
    Objects.requireNonNull(workItem, "workItem");

    final var tasksForAgent =
      this.agentTasks.stream()
        .filter(t -> Objects.equals(t.agentId(), agent))
        .toList();

    for (final var task : tasksForAgent) {
      if (task.offerWorkItem(workItem)) {
        return true;
      }
    }

    return false;
  }

  @Override
  public boolean sendWorkItem(
    final NPAgentID agent,
    final NPAgentWorkItem workItem)
  {
    Objects.requireNonNull(agent, "agent");
    Objects.requireNonNull(workItem, "workItem");

    final var tasksForAgent =
      this.agentTasks.stream()
        .filter(t -> Objects.equals(t.agentId(), agent))
        .toList();

    for (final var task : tasksForAgent) {
      if (task.sendWorkItem(workItem)) {
        return true;
      }
    }

    return false;
  }

  private void run()
  {
    LOG.info(
      "Starting Agent service on {}:{}",
      this.configuration.agentConfiguration().localAddress(),
      Integer.valueOf(this.configuration.agentConfiguration().localPort())
    );

    /*
     * Schedule a task that will instruct all connected agents to perform a
     * latency check periodically.
     */

    this.metrics.setAgentsConnected(0);
    this.agentTicker.scheduleAtFixedRate(
      this::onAgentTasksMeasureLatency,
      1L,
      1L,
      TimeUnit.SECONDS
    );

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

  private void onAgentTasksMeasureLatency()
  {
    this.agentTasks.forEach(task -> {
      if (!task.isClosed()) {
        task.runLatencyCheck();
      }
    });
  }

  private void createAndRunAgentTask(
    final Socket clientSocket)
  {
    try (var task = NPAgentTask.create(this.services, clientSocket)) {
      this.onAgentTaskCreated(task);
      task.run();
    } catch (final Exception e) {
      LOG.debug("Agent: ", e);
    } finally {
      this.onAgentTaskClosed();
    }
  }

  private void onAgentTaskClosed()
  {
    this.agentTasks.removeIf(NPAgentTask::isClosed);
    this.metrics.setAgentsConnected(this.agentTasks.size());
  }

  private void onAgentTaskCreated(
    final NPAgentTask task)
  {
    this.agentTasks.add(task);
    this.agentTasks.removeIf(NPAgentTask::isClosed);
    this.metrics.setAgentsConnected(this.agentTasks.size());
  }

  private ServerSocket openSocket()
    throws IOException
  {
    final var c =
      this.configuration.agentConfiguration();

    final var newSocket =
      this.sockets.createSocket();

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

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
