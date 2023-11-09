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


package com.io7m.northpike.agent.internal.console;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentConsoleConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.internal.NPAgentResources;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;

import static java.net.StandardSocketOptions.SO_REUSEADDR;
import static java.net.StandardSocketOptions.SO_REUSEPORT;

/**
 * The console service.
 */

public final class NPAConsoleService implements NPAConsoleServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAConsoleService.class);

  private final RPServiceDirectoryType services;
  private final NPStrings strings;
  private final NPAgentConsoleConfiguration configuration;
  private final AtomicBoolean closed;
  private CloseableCollectionType<NPAgentException> resources;
  private ServerSocket socket;
  private final ConcurrentHashMap.KeySetView<NPAConsoleTask, Boolean> consoleTasks;

  private NPAConsoleService(
    final RPServiceDirectoryType inServices,
    final NPStrings inStrings,
    final NPAgentConsoleConfiguration inConfiguration)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.closed =
      new AtomicBoolean(true);
    this.resources =
      NPAgentResources.createResources();
    this.consoleTasks =
      ConcurrentHashMap.newKeySet();
  }

  /**
   * The console service.
   *
   * @param services      The services
   * @param configuration The console configuration
   *
   * @return A service
   */

  public static NPAConsoleServiceType create(
    final RPServiceDirectoryType services,
    final NPAgentConsoleConfiguration configuration)
  {
    final var strings =
      services.requireService(NPStrings.class);

    return new NPAConsoleService(services, strings, configuration);
  }

  @Override
  public String description()
  {
    return "Agent console service.";
  }

  @Override
  public void start()
    throws Exception
  {
    if (this.closed.compareAndSet(true, false)) {
      this.resources =
        NPAgentResources.createResources();
      this.socket =
        this.resources.add(new ServerSocket());

      try {
        this.socket.setOption(SO_REUSEPORT, Boolean.TRUE);
      } catch (final UnsupportedOperationException e) {
        // Nothing we can do about this.
      }

      try {
        this.socket.setOption(SO_REUSEADDR, Boolean.TRUE);
      } catch (final UnsupportedOperationException e) {
        // Nothing we can do about this.
      }

      this.socket.bind(
        new InetSocketAddress(
          this.configuration.address(),
          this.configuration.port()
        )
      );

      Thread.ofVirtual()
        .start(this::runLoop);
    }
  }

  private void runLoop()
  {
    while (!this.closed.get()) {
      try {
        if (this.socket.isClosed()) {
          return;
        }

        final var client =
          this.socket.accept();

        Thread.ofVirtual()
          .start(() -> {
            try (
              var task =
                this.resources.add(
                  NPAConsoleTask.create(
                    this.services,
                    this.configuration,
                    client
                  )
                )
            ) {
              task.run();
            } catch (final Exception e) {
              LOG.debug("Console: ", e);
            }
          });

      } catch (final IOException e) {
        throw new RuntimeException(e);
      }
    }
  }

  @Override
  public String toString()
  {
    return "[NPAConsoleService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }
}
