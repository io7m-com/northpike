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
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.server.internal.tls.NPTLSContext;
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
import java.security.GeneralSecurityException;
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
  private CompletableFuture<Void> future;
  private NPServerConfiguration configuration;
  private final CloseableCollectionType<NPServerException> resources;

  private NPArchiveService(
    final NPServerConfiguration inConfiguration,
    final CloseableCollectionType<NPServerException> inResources,
    final ExecutorService inMainExecutor,
    final NPDatabaseType inDatabase)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.executor =
      Objects.requireNonNull(inMainExecutor, "mainExecutor");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
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
      database
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

  private void run()
  {
    LOG.info(
      "Starting Archive service on {}:{}",
      this.configuration.archiveConfiguration().localAddress(),
      Integer.valueOf(this.configuration.archiveConfiguration().localPort())
    );

    while (!this.closed.get()) {
      final var server = new Server();
      try {
        this.resources.add(server::stop);

        final var connector =
          this.createConnector(server);

        server.addConnector(connector);
        server.setErrorHandler(new NPErrorHandler());
        server.setHandler(
          new NPArchiveHandler(this.database, this.configuration.directories())
        );
        server.start();
        this.future.complete(null);

        while (!this.closed.get()) {
          Thread.sleep(1_000L);
        }
      } catch (final Exception e) {
        this.future.completeExceptionally(e);
        LOG.error("Failed to run server: ", e);
      }
    }
  }

  private Connector createConnector(
    final Server server)
    throws GeneralSecurityException, IOException
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

      sslContextFactory.setSslContext(
        NPTLSContext.create(
          "ArchiveService",
          config.keyStore(),
          config.trustStore()
        )
      );

      final var sslConnectionFactory =
        new SslConnectionFactory(
          sslContextFactory,
          HttpVersion.HTTP_1_1.asString()
        );

      final var connector =
        new ServerConnector(
          server,
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
        new ServerConnector(server, connectionFactory);

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
      this.resources.close();
      this.future.complete(null);
    }
  }
}
