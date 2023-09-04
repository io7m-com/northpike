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
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.tls.NPTLSContextServiceType;
import com.io7m.northpike.tls.NPTLSContext;
import com.io7m.northpike.tls.NPTLSDisabled;
import com.io7m.northpike.tls.NPTLSEnabled;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.eclipse.jetty.http.HttpVersion;
import org.eclipse.jetty.server.Connector;
import org.eclipse.jetty.server.Handler;
import org.eclipse.jetty.server.HttpConfiguration;
import org.eclipse.jetty.server.HttpConnectionFactory;
import org.eclipse.jetty.server.Request;
import org.eclipse.jetty.server.Response;
import org.eclipse.jetty.server.SecureRequestCustomizer;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.server.ServerConnector;
import org.eclipse.jetty.server.SslConnectionFactory;
import org.eclipse.jetty.util.Callback;
import org.eclipse.jetty.util.ssl.SslContextFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;

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
  private CompletableFuture<Void> future;
  private NPServerConfiguration configuration;
  private final CloseableCollectionType<NPServerException> resources;
  private NPTLSContext tlsContext;
  private Server server;

  private NPArchiveService(
    final NPServerConfiguration inConfiguration,
    final CloseableCollectionType<NPServerException> inResources,
    final ExecutorService inMainExecutor,
    final NPDatabaseType inDatabase,
    final NPTLSContextServiceType inTlsService)
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

    final var resources =
      NPServerResources.createResources();

    final var mainExecutor =
      Executors.newSingleThreadExecutor(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.server.archive.service[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    resources.add(mainExecutor::shutdown);

    return new NPArchiveService(
      configurations.configuration(),
      resources,
      mainExecutor,
      database,
      tlsService
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
    this.server = new Server();
    this.resources.add(this.server::stop);

    final var connector = this.createConnector();
    this.server.addConnector(connector);
    this.server.setErrorHandler(new NPErrorHandler());
    this.server.setHandler(
      new NPArchiveHandler(this.database, this.configuration.directories())
    );

    this.server.start();

    /*
     * Wait for the server to indicate that it has started. If the server
     * indicates failure, raise an exception. The startup will be retried
     * shortly.
     */

    while (!this.server.isStarted() && !this.closed.get()) {
      if (this.server.isFailed()) {
        throw new IOException("Server failed to start!");
      }
      pauseBriefly();
    }
  }

  private static void pauseBriefly()
  {
    try {
      Thread.sleep(1_000L);
    } catch (final InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  private Connector createConnector()
    throws NPServerException
  {
    final var archiveConfiguration =
      this.configuration.archiveConfiguration();
    final var tls =
      archiveConfiguration.tls();

    final var localAddress =
      new InetSocketAddress(
        archiveConfiguration.localAddress(),
        archiveConfiguration.localPort()
      );

    if (tls instanceof final NPTLSEnabled config) {
      final var sslContextFactory =
        new SslContextFactory.Server();

      final var httpsConfig = new HttpConfiguration();
      httpsConfig.setLocalAddress(localAddress);
      httpsConfig.addCustomizer(new SecureRequestCustomizer());
      httpsConfig.setSendServerVersion(false);
      httpsConfig.setSendXPoweredBy(false);

      this.tlsContext =
        this.tlsService.create(
          "ArchiveService",
          config.keyStore(),
          config.trustStore()
        );

      sslContextFactory.setSslContext(this.tlsContext.context());

      final var sslConnectionFactory =
        new SslConnectionFactory(
          sslContextFactory,
          HttpVersion.HTTP_1_1.asString()
        );

      final var connector =
        new ServerConnector(
          this.server,
          sslConnectionFactory,
          new HttpConnectionFactory(httpsConfig)
        );

      connector.setReuseAddress(true);
      connector.setReusePort(true);
      connector.setPort(archiveConfiguration.localPort());
      return connector;
    }

    if (tls instanceof NPTLSDisabled) {
      final var httpConfig = new HttpConfiguration();
      httpConfig.setLocalAddress(localAddress);
      httpConfig.setSendServerVersion(false);
      httpConfig.setSendXPoweredBy(false);

      final var connectionFactory =
        new HttpConnectionFactory(httpConfig);
      final var connector =
        new ServerConnector(this.server, connectionFactory);

      connector.setReuseAddress(true);
      connector.setReusePort(true);
      connector.setPort(archiveConfiguration.localPort());
      return connector;
    }

    throw new IllegalStateException();
  }

  private static final class NPErrorHandler extends Handler.Abstract
  {
    private NPErrorHandler()
    {

    }

    @Override
    public boolean handle(
      final Request request,
      final Response response,
      final Callback callback)
    {
      response.setStatus(400);
      response.write(
        true,
        ByteBuffer.wrap("ERROR".getBytes(StandardCharsets.UTF_8)),
        callback
      );
      return true;
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
    return this.server.isStopped();
  }
}
