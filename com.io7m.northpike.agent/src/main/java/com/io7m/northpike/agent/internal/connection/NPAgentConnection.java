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

import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairType;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeCompletion;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tls.NPTLSContextServiceType;

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
   * @param strings           The strings
   * @param tlsContexts       The TLS context service
   * @param keyPair           The agent's keypair
   * @param serverDescription The server description
   *
   * @return An open, authenticated connection
   *
   * @throws IOException          On I/O errors
   * @throws NPException          On errors
   * @throws InterruptedException On interruption
   */

  public static NPAgentConnectionType open(
    final NPStrings strings,
    final NPTLSContextServiceType tlsContexts,
    final NPAgentKeyPairType keyPair,
    final NPAgentServerDescription serverDescription)
    throws NPException, InterruptedException, IOException
  {
    final var publicKey =
      keyPair.publicKey();
    final var privateKey =
      keyPair.privateKey();

    final var connection =
      new NPAgentConnection(
        NPAgentConnectionHandlers.openConnectionHandler(
          strings,
          tlsContexts,
          serverDescription
        )
      );

    try {
      final var challenge =
        startLoginChallenge(strings, publicKey, connection);
      final var signature =
        privateKey.signData(challenge.challenge().data());

      return finishLoginChallenge(
        strings,
        challenge.challenge(),
        signature,
        connection
      );
    } catch (final Exception e) {
      connection.close();
      throw e;
    }
  }

  private static NPAgentConnectionType finishLoginChallenge(
    final NPStrings strings,
    final NPAgentLoginChallenge challenge,
    final byte[] signature,
    final NPAgentConnection connection)
    throws NPException, IOException, InterruptedException
  {
    final var response =
      connection.ask(
        NPACommandCLoginComplete.of(
          new NPAgentLoginChallengeCompletion(challenge.id(), signature)
        )
      );

    if (response instanceof final NPAResponseError error) {
      throw new NPAgentException(
        error.message(),
        error.errorCode(),
        error.attributes(),
        Optional.empty()
      );
    }

    if (response instanceof NPAResponseOK) {
      return connection;
    }

    throw errorUnexpectedMessage(
      strings,
      NPAResponseOK.class,
      response
    );
  }

  private static NPAResponseLoginChallenge startLoginChallenge(
    final NPStrings strings,
    final NPAgentKeyPublicType key,
    final NPAgentConnection connection)
    throws NPException, InterruptedException, IOException
  {
    final var response =
      connection.ask(NPACommandCLogin.of(key));

    if (response instanceof final NPAResponseError error) {
      throw new NPAgentException(
        error.message(),
        error.errorCode(),
        error.attributes(),
        Optional.empty()
      );
    }

    if (response instanceof final NPAResponseLoginChallenge challenge) {
      return challenge;
    }

    throw errorUnexpectedMessage(
      strings,
      NPAResponseLoginChallenge.class,
      response
    );
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
