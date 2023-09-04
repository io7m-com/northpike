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


package com.io7m.northpike.user_client.internal;

import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponseType;
import com.io7m.northpike.user_client.api.NPUserClientException;

import java.io.IOException;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.user_client.internal.NPUserExceptions.errorUnexpectedMessage;

/**
 * A connection from this user client to the server.
 */

public final class NPUserConnection
  extends NPMessageConnectionAbstract<NPUMessageType, NPUResponseType>
  implements NPUserConnectionType
{
  private NPUserConnection(
    final NPUserConnectionHandlerType inHandler)
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

  public static NPUserConnectionType open(
    final NPUserConnectionParameters configuration)
    throws NPException, InterruptedException, IOException
  {
    final var connection =
      new NPUserConnection(
        NPUserConnectionHandlers.openConnectionHandler(configuration)
      );

    try {
      final var response =
        connection.ask(NPUCommandLogin.of(
          configuration.userName(),
          configuration.password()
        ));

      if (response instanceof final NPUResponseOK ok) {
        return connection;
      }

      if (response instanceof final NPUResponseError error) {
        throw new NPUserClientException(
          error.message(),
          error.errorCode(),
          error.attributes(),
          Optional.empty()
        );
      }

      throw errorUnexpectedMessage(
        configuration.configuration().strings(),
        NPUResponseOK.class,
        response
      );
    } catch (final Exception e) {
      connection.close();
      throw e;
    }
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
