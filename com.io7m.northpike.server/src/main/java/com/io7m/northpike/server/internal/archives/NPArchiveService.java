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


package com.io7m.northpike.server.internal.archives;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPArchiveLinks;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import io.helidon.common.tls.TlsConfig;
import io.helidon.webserver.WebServer;
import io.helidon.webserver.WebServerConfig;
import io.helidon.webserver.http.HttpRouting;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.nio.file.Files;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;

import static java.net.StandardSocketOptions.SO_REUSEADDR;
import static java.net.StandardSocketOptions.SO_REUSEPORT;

/**
 * The archive service. A static web server that serves archive files
 * from a single directory.
 */

public final class NPArchiveService implements NPArchiveServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPArchiveService.class);

  private final AtomicBoolean closed;
  private final ExecutorService executor;
  private final NPDatabaseType database;
  private final NPTLSContextServiceType tlsService;
  private final NPMetricsServiceType metrics;
  private CompletableFuture<Void> future;
  private NPServerConfiguration configuration;
  private final CloseableCollectionType<NPServerException> resources;
  private WebServer webServer;

  private NPArchiveService(
    final NPServerConfiguration inConfiguration,
    final CloseableCollectionType<NPServerException> inResources,
    final ExecutorService inMainExecutor,
    final NPDatabaseType inDatabase,
    final NPTLSContextServiceType inTlsService,
    final NPMetricsServiceType inMetrics)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.executor =
      Objects.requireNonNull(inMainExecutor, "mainExecutor");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.tlsService =
      Objects.requireNonNull(inTlsService, "tlsService");
    this.metrics =
      Objects.requireNonNull(inMetrics, "metrics");
    this.closed =
      new AtomicBoolean(true);
    this.future =
      new CompletableFuture<>();
  }

  /**
   * Create an archive service.
   *
   * @param services The service directory
   *
   * @return An archive service
   */

  public static NPArchiveServiceType create(
    final RPServiceDirectoryType services)
  {
    final var configurations =
      services.requireService(NPConfigurationServiceType.class);
    final var tlsService =
      services.requireService(NPTLSContextServiceType.class);
    final var database =
      services.requireService(NPDatabaseType.class);
    final var metrics =
      services.requireService(NPMetricsServiceType.class);

    final var resources =
      NPServerResources.createResources();

    final var mainExecutor =
      resources.add(
        Executors.newThreadPerTaskExecutor(
          Thread.ofVirtual()
            .name("com.io7m.northpike.archive-", 0L)
            .factory()
        )
      );

    return new NPArchiveService(
      configurations.configuration(),
      resources,
      mainExecutor,
      database,
      tlsService,
      metrics
    );
  }

  @Override
  public CompletableFuture<Void> start()
  {
    if (this.closed.compareAndSet(true, false)) {
      this.executor.execute(this::run);
    }
    return this.future;
  }

  @Override
  public NPArchiveLinks linksForArchive(
    final NPArchive archive)
  {
    final var baseURI =
      this.configuration.archiveConfiguration().advertiseURI();

    return new NPArchiveLinks(
      baseURI.resolve(archive.fileName()),
      baseURI.resolve(archive.checksumFileName())
    );
  }

  @Override
  public void deleteArchive(
    final NPToken token)
    throws IOException
  {
    final var file =
      this.configuration.directories()
        .archiveDirectory()
        .resolve(NPArchive.fileNameFor(token));

    Files.deleteIfExists(file);
  }

  private void run()
  {
    LOG.info(
      "Starting Archive service on {}:{}",
      this.configuration.archiveConfiguration().localAddress(),
      Integer.valueOf(this.configuration.archiveConfiguration().localPort())
    );

    while (!this.closed.get()) {
      try {
        try {
          this.startServer();
        } catch (final Exception e) {
          LOG.error("Failed to start server, retrying shortly: ", e);
          pauseBriefly();
          continue;
        }

        this.future.complete(null);

        while (!this.closed.get()) {
          pauseBriefly();
        }
      } catch (final Exception e) {
        this.future.completeExceptionally(e);
        LOG.error("Failed to run server: ", e);
      }
    }
  }

  private void startServer()
    throws Exception
  {
    final var httpConfig =
      this.configuration.archiveConfiguration();
    final var address =
      new InetSocketAddress(
        httpConfig.localAddress(),
        httpConfig.localPort()
      );

    final var handler =
      new NPArchiveHandler(
        this.metrics,
        this.database,
        this.configuration.directories()
      );

    final var routing = HttpRouting.builder();
    routing.get("/", handler);
    routing.get("/*", handler);

    final var webServerBuilder =
      WebServerConfig.builder();

    if (httpConfig.tls() instanceof final NPTLSEnabledExplicit enabled) {
      final var tlsContext =
        this.tlsService.create(
          "Archive",
          enabled.keyStore(),
          enabled.trustStore()
        );

      webServerBuilder.tls(
        TlsConfig.builder()
          .enabled(true)
          .sslContext(tlsContext.context())
          .build()
      );
    }

    this.webServer =
      webServerBuilder.port(httpConfig.localPort())
        .address(httpConfig.localAddress())
        .routing(routing)
        .listenerSocketOptions(Map.ofEntries(
          Map.entry(SO_REUSEADDR, Boolean.TRUE),
          Map.entry(SO_REUSEPORT, Boolean.TRUE)
        ))
        .build();

    this.resources.add(this.webServer::stop);
    this.webServer.start();

    for (int index = 0; index < 30; ++index) {
      if (!this.webServer.isRunning()) {
        pauseBriefly();
      }
    }

    if (!this.webServer.isRunning()) {
      throw new IllegalStateException("Server could not be started.");
    }

    LOG.info("[{}] Archive server started", address);
  }

  private static void pauseBriefly()
  {
    try {
      Thread.sleep(1_000L);
    } catch (final InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String description()
  {
    return "Archive service.";
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      LOG.debug("Shutting down archive service.");
      this.resources.close();

      while (!this.isStopped()) {
        LOG.debug("Waiting for archive service to shut down...");
        pauseBriefly();
      }

      LOG.debug("Archive service is down.");
      this.future.complete(null);
    }
  }

  private boolean isStopped()
  {
    return !this.webServer.isRunning();
  }

  @Override
  public String toString()
  {
    return "[NPArchiveService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
