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


package com.io7m.northpike.server.internal.agents;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.northpike.connections.NPMessageConnectionAbstract;
import com.io7m.northpike.connections.NPMessageHandlerType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorNoSupportedProtocols;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL_UNSUPPORTED;

/**
 * A connection from a remote agent to this server.
 */

public final class NPAgentServerConnection
  extends NPMessageConnectionAbstract<NPAMessageType, NPAResponseType>
  implements NPAgentServerConnectionType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentServerConnection.class);

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();
  private static final NPIProtocol NPA_1 =
    new NPIProtocol(NPA1Messages.protocolId(), 1L);

  private final NPStrings strings;
  private final Socket socket;
  private final InputStream input;
  private final OutputStream output;
  private final InetSocketAddress remoteAddress;
  private final NPServerAgentConfiguration configuration;

  /**
   * A connection from a remote agent to this server.
   *
   * @param inStrings       The string resources
   * @param inConfiguration The configuration
   * @param inSocket        The socket
   *
   * @throws IOException On errors
   */

  public NPAgentServerConnection(
    final NPStrings inStrings,
    final NPServerAgentConfiguration inConfiguration,
    final Socket inSocket)
    throws IOException
  {
    super(
      LOG,
      CloseableCollection.create(() -> {
        return new NPServerException(
          "One or more resources could not be closed.",
          new NPErrorCode("resources"),
          Map.of(),
          Optional.empty()
        );
      })
    );

    this.strings =
      Objects.requireNonNull(inStrings, "inStrings");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.socket =
      Objects.requireNonNull(inSocket, "inSocket");
    this.input =
      this.socket.getInputStream();
    this.output =
      this.socket.getOutputStream();
    this.remoteAddress =
      new InetSocketAddress(
        this.socket.getInetAddress(),
        this.socket.getPort()
      );
  }

  @Override
  protected UUID onFindMessageID(
    final NPAMessageType message)
  {
    return message.messageID();
  }

  @Override
  protected UUID onFindCorrelationID(
    final NPAResponseType message)
  {
    return message.correlationID();
  }

  @Override
  protected NPMessageHandlerType<NPAMessageType> onConnect()
    throws NPServerException
  {
    try {
      NPI_MESSAGES.writeLengthPrefixed(
        this.output,
        new NPIProtocolsAvailable(List.of(NPA_1))
      );

      final var proto = this.readNPISpecific(NPIProtocol.class);
      if (Objects.equals(proto, NPA_1)) {
        NPI_MESSAGES.writeLengthPrefixed(this.output, NPA_1);
        return new NPAgentServerConnectionHandler1(
          this.configuration.messageSizeLimit(),
          this.strings,
          this.input,
          this.output
        );
      }

      this.sendError(ERROR_PROTOCOL_UNSUPPORTED, errorNoSupportedProtocols());
      throw this.exErrorUnsupported();
    } catch (final NPProtocolException e) {
      throw NPServerExceptions.errorProtocol(e);
    } catch (final IOException e) {
      throw NPServerExceptions.errorIO(this.strings, e);
    }
  }

  @Override
  protected NPAResponseType onCheckIfMessageIsResponse(
    final NPAMessageType message)
  {
    if (message instanceof final NPAResponseType response) {
      return response;
    }
    return null;
  }

  private <T extends NPIMessageType> T readNPISpecific(
    final Class<T> clazz)
    throws NPServerException, IOException, NPProtocolException
  {
    final var m0 = NPI_MESSAGES.readLengthPrefixed(this.input);
    if (clazz.isAssignableFrom(m0.getClass())) {
      return clazz.cast(m0);
    }
    this.sendError(ERROR_PROTOCOL, errorProtocol());
    throw this.exErrorProtocol();
  }

  private void sendError(
    final NPStringConstants constant,
    final NPErrorCode errorCode)
    throws NPProtocolException, IOException
  {
    NPI_MESSAGES.writeLengthPrefixed(
      this.output,
      new NPIError(errorCode, this.strings.format(constant))
    );
  }

  private NPServerException exErrorUnsupported()
  {
    return new NPServerException(
      this.strings.format(ERROR_PROTOCOL_UNSUPPORTED),
      errorNoSupportedProtocols(),
      Map.of(),
      Optional.empty()
    );
  }

  private NPServerException exErrorProtocol()
  {
    return new NPServerException(
      this.strings.format(ERROR_PROTOCOL),
      errorProtocol(),
      Map.of(),
      Optional.empty()
    );
  }

  @Override
  public InetSocketAddress remoteAddress()
  {
    return this.remoteAddress;
  }
}
