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

import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.tls.NPTLSContext;
import com.io7m.northpike.server.internal.tls.NPTLSContextServiceType;
import com.io7m.northpike.tls.NPTLSDisabled;
import com.io7m.northpike.tls.NPTLSEnabled;

import javax.net.ServerSocketFactory;
import java.io.IOException;
import java.net.ServerSocket;
import java.util.Objects;
import java.util.Optional;

/**
 * The socket service for agents.
 */

public final class NPAgentServerSocketService
  implements NPAgentServerSocketServiceType
{
  private final Optional<NPTLSContext> context;
  private final ServerSocketFactory sockets;

  private NPAgentServerSocketService(
    final Optional<NPTLSContext> inContext,
    final ServerSocketFactory inSockets)
  {
    this.context =
      Objects.requireNonNull(inContext, "context");
    this.sockets =
      Objects.requireNonNull(inSockets, "sockets");
  }

  /**
   * The socket service for agents.
   *
   * @param tlsService    The TLS service
   * @param configuration The configuration
   *
   * @return A socket service
   *
   * @throws NPServerException On errors
   */

  public static NPAgentServerSocketServiceType create(
    final NPTLSContextServiceType tlsService,
    final NPServerAgentConfiguration configuration)
    throws NPServerException
  {
    Objects.requireNonNull(configuration, "configuration");

    final var tls = configuration.tls();
    if (tls instanceof NPTLSDisabled) {
      return new NPAgentServerSocketService(
        Optional.empty(),
        ServerSocketFactory.getDefault()
      );
    }

    if (tls instanceof final NPTLSEnabled enabled) {
      final var tlsContext =
        tlsService.create(
          "AgentService",
          enabled.keyStore(),
          enabled.trustStore()
        );

      return new NPAgentServerSocketService(
        Optional.of(tlsContext),
        tlsContext.context().getServerSocketFactory()
      );
    }

    throw new IllegalStateException();
  }

  @Override
  public ServerSocket createSocket()
    throws IOException
  {
    return this.sockets.createServerSocket();
  }

  @Override
  public String description()
  {
    return "Agent server socket service.";
  }
}
