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

import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.Objects;
import java.util.UUID;

/**
 * A connection from a remote agent to this server.
 */

public final class NPAConsoleServerConnection
  extends NPMessageConnectionAbstract<NPACMessageType, NPACResponseType>
  implements NPAConsoleServerConnectionType
{
  private final InetSocketAddress remoteAddress;

  private NPAConsoleServerConnection(
    final InetSocketAddress inRemoteAddress,
    final NPAConsoleServerConnectionHandlerType inHandler)
  {
    super(inHandler);

    this.remoteAddress =
      Objects.requireNonNull(inRemoteAddress, "remoteAddress");
  }

  /**
   * A connection from a remote agent to this server.
   *
   * @param strings The string resources
   * @param socket  The socket
   *
   * @return A connection
   *
   * @throws NPException On errors
   * @throws IOException On errors
   */

  public static NPAConsoleServerConnectionType open(
    final NPStrings strings,
    final Socket socket)
    throws NPException, IOException
  {
    return new NPAConsoleServerConnection(
      new InetSocketAddress(
        socket.getInetAddress(),
        socket.getPort()
      ),
      NPAConsoleServerConnectionHandlers.open(strings, socket)
    );
  }

  @Override
  public InetSocketAddress remoteAddress()
  {
    return this.remoteAddress;
  }

  @Override
  protected NPACResponseType isResponse(
    final NPACMessageType message)
  {
    if (message instanceof final NPACResponseType r) {
      return r;
    }
    return null;
  }

  @Override
  protected UUID messageID(
    final NPACMessageType message)
  {
    return message.messageID();
  }

  @Override
  protected UUID correlationID(
    final NPACResponseType message)
  {
    return message.correlationID();
  }
}
