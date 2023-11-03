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

package com.io7m.northpike.agent.console_client.internal;

import com.io7m.northpike.agent.console_client.api.NPAConsoleClientConfiguration;
import com.io7m.northpike.connections.NPMessageConnectionHandlerAbstract;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.cb.NPACMessages;

import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

/**
 * The agent handler for protocol version 1.
 */

public final class NPAConsoleConnectionHandler1
  extends NPMessageConnectionHandlerAbstract<NPACMessageType>
  implements NPAConsoleConnectionHandlerType
{
  private static final NPACMessages MESSAGES =
    new NPACMessages();

  NPAConsoleConnectionHandler1(
    final NPAConsoleClientConfiguration configuration,
    final Socket inSocket,
    final InputStream inInputStream,
    final OutputStream inOutputStream)
  {
    super(
      MESSAGES,
      configuration.strings(),
      Integer.MAX_VALUE,
      inSocket,
      inInputStream,
      inOutputStream
    );
  }
}
