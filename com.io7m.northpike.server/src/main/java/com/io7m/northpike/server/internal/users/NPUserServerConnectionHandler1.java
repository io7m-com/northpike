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

import com.io7m.northpike.connections.NPMessageConnectionHandlerAbstract;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.cb.NPU1Messages;
import com.io7m.northpike.strings.NPStrings;

import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

/**
 * The server handler for protocol version 1.
 */

public final class NPUserServerConnectionHandler1
  extends NPMessageConnectionHandlerAbstract<NPUMessageType>
  implements NPUserServerConnectionHandlerType
{
  private static final NPU1Messages MESSAGES =
    new NPU1Messages();

  NPUserServerConnectionHandler1(
    final int inMessageSizeLimit,
    final NPStrings inStrings,
    final Socket inSocket,
    final InputStream inInputStream,
    final OutputStream inOutputStream)
  {
    super(
      MESSAGES,
      inStrings,
      inMessageSizeLimit,
      inSocket,
      inInputStream,
      inOutputStream
    );
  }
}
