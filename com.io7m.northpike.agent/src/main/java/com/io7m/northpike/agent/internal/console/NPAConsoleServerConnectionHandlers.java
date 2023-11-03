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

import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.cb.NPACMessages;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.net.Socket;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorNoSupportedProtocols;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL_UNSUPPORTED;

/**
 * Functions to create connection handlers.
 */

public final class NPAConsoleServerConnectionHandlers
{
  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();
  private static final NPIProtocol NPU_1 =
    new NPIProtocol(NPACMessages.protocolId(), 1L);

  private NPAConsoleServerConnectionHandlers()
  {

  }

  /**
   * Open a new connection handler.
   *
   * @param socket    The socket
   * @param strings   The string resources
   *
   * @return A new connection handler
   *
   * @throws NPException On errors
   */

  public static NPAConsoleServerConnectionHandlerType open(
    final NPStrings strings,
    final Socket socket)
    throws NPException, IOException
  {
    final var output =
      socket.getOutputStream();
    final var input =
      socket.getInputStream();

    /*
     * Advertise the available protocol versions.
     */

    NPI_MESSAGES.writeLengthPrefixed(
      output,
      new NPIProtocolsAvailable(List.of(NPU_1))
    );

    /*
     * Read a protocol version from the client, and either confirm the
     * selected version, or send an error and fail the connection.
     */

    final var r0 =
      NPI_MESSAGES.readLengthPrefixed(strings, Integer.MAX_VALUE, input);

    if (r0 instanceof final NPIProtocol proto) {
      if (Objects.equals(proto, NPU_1)) {
        NPI_MESSAGES.writeLengthPrefixed(output, NPU_1);
        return new NPAConsoleServerConnectionHandler1(
          strings, socket, input, output);
      }

      NPI_MESSAGES.writeLengthPrefixed(
        output,
        new NPIError(
          errorNoSupportedProtocols(),
          strings.format(ERROR_PROTOCOL_UNSUPPORTED)
        )
      );

      throw new NPAgentException(
        strings.format(ERROR_PROTOCOL_UNSUPPORTED),
        errorNoSupportedProtocols(),
        Map.of(),
        Optional.empty()
      );
    }

    NPI_MESSAGES.writeLengthPrefixed(
      output,
      new NPIError(
        errorProtocol(),
        strings.format(ERROR_PROTOCOL)
      )
    );

    throw new NPAgentException(
      strings.format(ERROR_PROTOCOL),
      errorProtocol(),
      Map.of(),
      Optional.empty()
    );
  }
}
