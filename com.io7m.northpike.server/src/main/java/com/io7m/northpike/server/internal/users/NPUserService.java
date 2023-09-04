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


package com.io7m.northpike.server.internal.users;

import com.io7m.jmulticlose.core.CloseableCollectionType;
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
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main agent service.
 */

public final class NPUserService implements NPUserServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPUserService.class);

  private final RPServiceDirectoryType services;
  private final CloseableCollectionType<NPServerException> resources;
  private final NPServerConfiguration configuration;
  private final NPEventServiceType events;
  private final NPMetricsServiceType metrics;
  private final NPUserServerSocketServiceType sockets;
  private final ExecutorService agentExecutor;
  private final AtomicBoolean closed;
  private final ExecutorService mainExecutor;
  private final CompletableFuture<Void> future;
  private final ConcurrentHashMap.KeySetView<NPUserTask, Boolean> userTasks;
  private ServerSocket socket;

  private NPUserService(
    final RPServiceDirectoryType inServices,
    final CloseableCollectionType<NPServerException> inResources,
    final NPServerConfiguration inConfiguration,
    final NPEventServiceType inEvents,
    final NPMetricsServiceType inMetrics,
    final NPUserServerSocketServiceType inSockets,
    final ExecutorService inMainExecutor,
    final ExecutorService inUserExecutor)
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
      Objects.requireNonNull(inUserExecutor, "agentExecutor");
    this.mainExecutor =
      Objects.requireNonNull(inMainExecutor, "inMainExecutor");
    this.closed =
      new AtomicBoolean(true);
    this.future =
      new CompletableFuture<>();
    this.userTasks =
      ConcurrentHashMap.newKeySet();
  }

  /**
   * Create an agent service.
   *
   * @param services The service directory
   *
   * @return The service
   */

  public static NPUserServiceType create(
    final RPServiceDirectoryType services)
  {
    Objects.requireNonNull(services, "services");

    final var configuration =
      services.requireService(NPConfigurationServiceType.class);
    final var events =
      services.requireService(NPEventServiceType.class);
    final var sockets =
      services.requireService(NPUserServerSocketServiceType.class);
    final var metrics =
      services.requireService(NPMetricsServiceType.class);

    final var resources =
      NPServerResources.createResources();

    final var mainExecutor =
      Executors.newSingleThreadExecutor(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.server.user.service[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    resources.add(mainExecutor::shutdown);

    final var agentExecutor =
      Executors.newCachedThreadPool(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.server.user[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    resources.add(agentExecutor::shutdown);

    return new NPUserService(
      services,
      resources,
      configuration.configuration(),
      events,
      metrics,
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
      "Starting User service on {}:{}",
      this.configuration.userConfiguration().localAddress(),
      Integer.valueOf(this.configuration.userConfiguration().localPort())
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

      this.events.emit(new NPUserServiceStarted());
      this.future.complete(null);

      /*
       * Repeatedly accept clients from the bound socket.
       */

      while (!this.closed.get()) {
        final Socket newSocket;
        try {
          newSocket = this.socket.accept();
          this.events.emit(new NPUserConnected(
            newSocket.getInetAddress(),
            newSocket.getPort()
          ));
        } catch (final Exception e) {
          LOG.error("Accept: ", e);
          continue;
        }

        this.agentExecutor.execute(() -> this.createAndRunUserTask(newSocket));
      }
    }
  }

  private void createAndRunUserTask(
    final Socket clientSocket)
  {
    try (var task = NPUserTask.create(this.services, clientSocket)) {
      this.onUserTaskCreated(task);
      task.run();
    } catch (final Exception e) {
      LOG.debug("User: ", e);
    } finally {
      this.onUserTaskClosed();
    }
  }

  private void onUserTaskClosed()
  {
    this.userTasks.removeIf(NPUserTask::isClosed);
    this.metrics.setUsersConnected(this.userTasks.size());
  }

  private void onUserTaskCreated(
    final NPUserTask task)
  {
    this.userTasks.add(task);
    this.userTasks.removeIf(NPUserTask::isClosed);
    this.metrics.setUsersConnected(this.userTasks.size());
  }

  private ServerSocket openSocket()
    throws IOException
  {
    final var c =
      this.configuration.userConfiguration();

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
    return "The user service.";
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
    return "[NPUserService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }
}
