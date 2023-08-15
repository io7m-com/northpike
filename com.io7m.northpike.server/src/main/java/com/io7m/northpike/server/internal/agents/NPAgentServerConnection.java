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

import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.Objects;
import java.util.UUID;

/**
 * A connection from a remote agent to this server.
 */

public final class NPAgentServerConnection
  extends NPMessageConnectionAbstract<NPAMessageType, NPAResponseType>
  implements NPAgentServerConnectionType
{
  private final InetSocketAddress remoteAddress;

  private NPAgentServerConnection(
    final InetSocketAddress inRemoteAddress,
    final NPAgentServerConnectionHandlerType inHandler)
  {
    super(inHandler);

    this.remoteAddress =
      Objects.requireNonNull(inRemoteAddress, "remoteAddress");
  }

  /**
   * A connection from a remote agent to this server.
   *
   * @param strings   The string resources
   * @param socket    The socket
   * @param sizeLimit The size limit
   *
   * @return A connection
   *
   * @throws NPException On errors
   * @throws IOException On errors
   */

  public static NPAgentServerConnectionType open(
    final NPStrings strings,
    final int sizeLimit,
    final Socket socket)
    throws NPException, IOException
  {
    return new NPAgentServerConnection(
      new InetSocketAddress(
        socket.getInetAddress(),
        socket.getPort()
      ),
      NPAgentServerConnectionHandlers.open(strings, sizeLimit, socket)
    );
  }

  @Override
  public InetSocketAddress remoteAddress()
  {
    return this.remoteAddress;
  }

  @Override
  protected NPAResponseType isResponse(
    final NPAMessageType message)
  {
    if (message instanceof final NPAResponseType r) {
      return r;
    }
    return null;
  }

  @Override
  protected UUID messageID(
    final NPAMessageType message)
  {
    return message.messageID();
  }

  @Override
  protected UUID correlationID(
    final NPAResponseType message)
  {
    return message.correlationID();
  }
}
