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

package com.io7m.northpike.agent.internal;

import com.io7m.genevan.core.GenProtocolClientHandlerType;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.strings.NPStrings;

import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

/**
 * The type of protocol handler factories.
 */

public interface NPAgentConnectionHandlerFactoryType
  extends GenProtocolClientHandlerType
{
  /**
   * Create a new handler.
   *
   * @param strings       String resources for error messages
   * @param configuration The configuration
   * @param socket        The socket
   * @param inputStream   The input stream
   * @param outputStream  The output stream
   *
   * @return A new handler
   */

  NPAgentConnectionHandlerType createHandler(
    NPStrings strings,
    NPAgentConfiguration configuration,
    Socket socket,
    InputStream inputStream,
    OutputStream outputStream
  );
}
