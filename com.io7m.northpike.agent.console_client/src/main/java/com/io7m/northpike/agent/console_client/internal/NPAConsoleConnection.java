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



import com.io7m.northpike.agent.console_client.api.NPAConsoleClientException;
import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandLogin;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.NPACResponseError;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;

import java.io.IOException;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.agent.console_client.internal.NPAConsoleExceptions.errorUnexpectedMessage;

/**
 * A connection from this user client to the server.
 */

public final class NPAConsoleConnection
  extends NPMessageConnectionAbstract<NPACMessageType, NPACResponseType>
  implements NPAConsoleConnectionType
{
  private NPAConsoleConnection(
    final NPAConsoleConnectionHandlerType inHandler)
  {
    super(inHandler);
  }

  /**
   * Open a connection to the server and attempt to authenticate. If the
   * connection or authentication fails, all resources are released.
   *
   * @param configuration The user client configuration
   *
   * @return An open, authenticated connection
   *
   * @throws NPException          On errors
   * @throws InterruptedException On interruption
   */

  public static NPAConsoleConnectionType open(
    final NPAConsoleConnectionParameters configuration)
    throws NPException, InterruptedException, IOException
  {
    final var connection =
      new NPAConsoleConnection(
        NPAConsoleConnectionHandlers.openConnectionHandler(configuration)
      );

    try {
      final var response =
        connection.ask(NPACCommandLogin.of(configuration.accessKey()));

      return switch (response) {
        case final NPACResponseOK ok -> {
          yield connection;
        }
        case final NPACResponseError error -> {
          throw new NPAConsoleClientException(
            error.message(),
            error.errorCode(),
            error.attributes(),
            Optional.empty()
          );
        }
        default -> {
          throw errorUnexpectedMessage(
            configuration.configuration().strings(),
            NPACResponseOK.class,
            response
          );
        }
      };
    } catch (final Exception e) {
      connection.close();
      throw e;
    }
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
