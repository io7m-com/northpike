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

import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseType;

import java.io.IOException;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.agent.internal.NPAgentExceptions.errorUnexpectedMessage;

/**
 * A connection from this agent to the server.
 */

public final class NPAgentConnection
  extends NPMessageConnectionAbstract<NPAMessageType, NPAResponseType>
  implements NPAgentConnectionType
{
  private NPAgentConnection(
    final NPAgentConnectionHandlerType inHandler)
  {
    super(inHandler);
  }

  /**
   * Open a connection to the server and attempt to authenticate. If the
   * connection or authentication fails, all resources are released.
   *
   * @param configuration The agent configuration
   *
   * @return An open, authenticated connection
   *
   * @throws NPException          On errors
   * @throws InterruptedException On interruption
   */

  public static NPAgentConnectionType open(
    final NPAgentConfiguration configuration)
    throws NPException, InterruptedException, IOException
  {
    final var connection =
      new NPAgentConnection(
        NPAgentConnectionHandlers.openConnectionHandler(configuration)
      );

    try {
      final var response =
        connection.ask(NPACommandCLogin.of(configuration.accessKey()));

      if (response instanceof final NPAResponseOK ok) {
        return connection;
      }

      if (response instanceof final NPAResponseError error) {
        throw new NPAgentException(
          error.message(),
          error.errorCode(),
          error.attributes(),
          Optional.empty()
        );
      }

      throw errorUnexpectedMessage(
        configuration.strings(),
        NPAResponseOK.class,
        response
      );
    } catch (final Exception e) {
      connection.close();
      throw e;
    }
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
