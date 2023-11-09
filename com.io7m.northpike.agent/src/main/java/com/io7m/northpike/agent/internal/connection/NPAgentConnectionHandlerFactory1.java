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

package com.io7m.northpike.agent.internal.connection;

import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolVersion;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.strings.NPStrings;

import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

import static java.math.BigInteger.ONE;
import static java.math.BigInteger.ZERO;

/**
 * The factory of version 1 protocol handlers.
 */

public final class NPAgentConnectionHandlerFactory1
  implements NPAgentConnectionHandlerFactoryType
{
  /**
   * The factory of version 1 protocol handlers.
   */

  public NPAgentConnectionHandlerFactory1()
  {

  }

  @Override
  public GenProtocolIdentifier supported()
  {
    return new GenProtocolIdentifier(
      NPA1Messages.protocolId().toString(),
      new GenProtocolVersion(ONE, ZERO)
    );
  }

  @Override
  public NPAgentConnectionHandlerType createHandler(
    final NPStrings strings,
    final NPAgentServerDescription configuration,
    final Socket socket,
    final InputStream inputStream,
    final OutputStream outputStream)
  {
    return new NPAgentConnectionHandler1(
      strings,
      configuration,
      socket,
      inputStream,
      outputStream
    );
  }
}
