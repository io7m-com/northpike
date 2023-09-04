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

import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseType;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.Objects;
import java.util.UUID;

/**
 * A connection from a remote agent to this server.
 */

public final class NPUserServerConnection
  extends NPMessageConnectionAbstract<NPUMessageType, NPUResponseType>
  implements NPUserServerConnectionType
{
  private final InetSocketAddress remoteAddress;

  private NPUserServerConnection(
    final InetSocketAddress inRemoteAddress,
    final NPUserServerConnectionHandlerType inHandler)
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

  public static NPUserServerConnectionType open(
    final NPStrings strings,
    final int sizeLimit,
    final Socket socket)
    throws NPException, IOException
  {
    return new NPUserServerConnection(
      new InetSocketAddress(
        socket.getInetAddress(),
        socket.getPort()
      ),
      NPUserServerConnectionHandlers.open(strings, sizeLimit, socket)
    );
  }

  @Override
  public InetSocketAddress remoteAddress()
  {
    return this.remoteAddress;
  }

  @Override
  protected NPUResponseType isResponse(
    final NPUMessageType message)
  {
    if (message instanceof final NPUResponseType r) {
      return r;
    }
    return null;
  }

  @Override
  protected UUID messageID(
    final NPUMessageType message)
  {
    return message.messageID();
  }

  @Override
  protected UUID correlationID(
    final NPUResponseType message)
  {
    return message.correlationID();
  }
}
