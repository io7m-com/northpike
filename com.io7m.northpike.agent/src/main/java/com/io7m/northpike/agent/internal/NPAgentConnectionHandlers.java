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

import com.io7m.genevan.core.GenProtocolException;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolServerEndpointType;
import com.io7m.genevan.core.GenProtocolSolved;
import com.io7m.genevan.core.GenProtocolSolver;
import com.io7m.genevan.core.GenProtocolVersion;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;

import javax.net.SocketFactory;
import javax.net.ssl.SSLSocketFactory;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.agent.internal.NPAgentExceptions.errorUnexpectedMessage;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_SERVER_FAILED_PROTOCOL_CONFIRMATION;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;

/**
 * Functions to create connection handlers.
 */

public final class NPAgentConnectionHandlers
{
  private static final SocketFactory SOCKETS =
    SocketFactory.getDefault();
  private static final SocketFactory SOCKETS_TLS =
    SSLSocketFactory.getDefault();
  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private NPAgentConnectionHandlers()
  {

  }

  /**
   * Open a new connection.
   *
   * @param configuration The configuration
   *
   * @return A new connection
   *
   * @throws NPAgentException On errors
   * @throws IOException      On errors
   */

  public static NPAgentConnectionHandlerType openConnection(
    final NPAgentConfiguration configuration)
    throws NPAgentException, IOException
  {
    final var socketAddress =
      new InetSocketAddress(
        configuration.remoteAddress(),
        configuration.remotePort()
      );

    final var socket =
      configuration.useTLS()
        ? SOCKETS_TLS.createSocket()
        : SOCKETS.createSocket();

    try {
      socket.setTcpNoDelay(true);
      socket.setPerformancePreferences(1, 2, 0);
      socket.connect(socketAddress, 10);
      return negotiateVersion(configuration, socket);
    } catch (final Exception e) {
      socket.close();
      throw e;
    }
  }

  private record NPServerEndpoint(
    GenProtocolIdentifier supported)
    implements GenProtocolServerEndpointType
  {
    NPServerEndpoint
    {
      Objects.requireNonNull(supported, "supported");
    }
  }

  private static NPAgentConnectionHandlerType negotiateVersion(
    final NPAgentConfiguration configuration,
    final Socket socket)
    throws IOException, NPAgentException
  {
    final var inputStream =
      socket.getInputStream();
    final var outputStream =
      socket.getOutputStream();

    final var available =
      readNPIMessageOfType(
        configuration,
        inputStream,
        NPIProtocolsAvailable.class
      );

    final GenProtocolSolved<NPAgentConnectionHandlerFactoryType, NPServerEndpoint> solved =
      solveVersion(available);

    final var solvedEndpoint =
      solved.serverEndpoint();

    final var chosen =
      new NPIProtocol(
        UUID.fromString(solvedEndpoint.supported.identifier()),
        solvedEndpoint.supported.version().versionMajor().longValue()
      );

    sendMessage(outputStream, chosen);

    final var confirmed =
      readNPIMessageOfType(
        configuration,
        inputStream,
        NPIProtocol.class
      );

    if (!chosen.equals(confirmed)) {
      throw errorServerFailedConfirmation(
        configuration.strings(),
        chosen,
        confirmed
      );
    }

    return solved.clientHandler()
      .createHandler(
        configuration,
        socket,
        inputStream,
        outputStream
      );
  }

  private static GenProtocolSolved<NPAgentConnectionHandlerFactoryType, NPServerEndpoint>
  solveVersion(
    final NPIProtocolsAvailable available)
    throws NPAgentException
  {
    final var supportedByServer =
      available.protocols()
        .stream()
        .map(p -> {
          return new NPServerEndpoint(
            new GenProtocolIdentifier(
              p.protocolId().toString(),
              new GenProtocolVersion(
                BigInteger.valueOf(p.protocolVersion()),
                BigInteger.ZERO
              )
            )
          );
        })
        .toList();

    final var supportedByClient =
      List.of(new NPAgentConnectionHandlerFactory1());

    final var solver =
      GenProtocolSolver.<NPAgentConnectionHandlerFactoryType, NPServerEndpoint>
        create(Locale.ROOT);

    final GenProtocolSolved<NPAgentConnectionHandlerFactoryType, NPServerEndpoint> solved;
    try {
      solved = solver.solve(
        supportedByServer,
        supportedByClient,
        List.of(NPA1Messages.protocolId().toString())
      );
    } catch (final GenProtocolException e) {
      throw new NPAgentException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorNoSupportedProtocols(),
        Map.of(),
        Optional.empty()
      );
    }
    return solved;
  }

  private static void sendMessage(
    final OutputStream outputStream,
    final NPIMessageType message)
    throws IOException
  {
    final var messageData = NPI_MESSAGES.serialize(message);
    final var sizeBytes = new byte[4];
    final var sizeBuffer = ByteBuffer.wrap(sizeBytes);
    sizeBuffer.order(ByteOrder.BIG_ENDIAN);
    sizeBuffer.putInt(0, messageData.length);

    outputStream.write(sizeBytes);
    outputStream.write(messageData);
    outputStream.flush();
  }

  private static <M extends NPIMessageType> M readNPIMessageOfType(
    final NPAgentConfiguration configuration,
    final InputStream inputStream,
    final Class<M> clazz)
    throws IOException, NPAgentException
  {
    final var strings =
      configuration.strings();
    final var message =
      readNPIMessage(configuration, inputStream);

    if (message instanceof final NPIError error) {
      throw new NPAgentException(
        error.errorMessage(),
        error.errorCode(),
        Map.of(),
        Optional.empty()
      );
    }

    if (!Objects.equals(clazz, message.getClass())) {
      throw errorUnexpectedMessage(strings, clazz, message);
    }

    return clazz.cast(message);
  }

  private static NPIMessageType readNPIMessage(
    final NPAgentConfiguration configuration,
    final InputStream inputStream)
    throws IOException, NPAgentException
  {
    final var strings = configuration.strings();
    final var sizeBytes = inputStream.readNBytes(4);
    if (sizeBytes.length != 4) {
      throw NPAgentExceptions.errorShortRead(strings, 4, sizeBytes.length);
    }

    final var sizeData = ByteBuffer.wrap(sizeBytes);
    sizeData.order(ByteOrder.BIG_ENDIAN);

    final var messageSize = sizeData.getInt(0);
    if (messageSize > configuration.messageSizeLimit()) {
      throw NPAgentExceptions.errorTooLarge(
        strings,
        messageSize,
        configuration.messageSizeLimit()
      );
    }

    final var messageData =
      inputStream.readNBytes(messageSize);

    try {
      return NPI_MESSAGES.parse(messageData);
    } catch (final NPProtocolException e) {
      throw NPAgentExceptions.errorProtocol(e);
    }
  }

  private static NPAgentException errorServerFailedConfirmation(
    final NPStrings strings,
    final NPIProtocol expected,
    final NPIProtocol confirmed)
  {
    return new NPAgentException(
      strings.format(ERROR_SERVER_FAILED_PROTOCOL_CONFIRMATION),
      NPStandardErrorCodes.errorIo(),
      Map.ofEntries(
        Map.entry(
          strings.format(EXPECTED),
          "%s %s".formatted(expected.protocolId(), expected.protocolVersion())
        ),
        Map.entry(
          strings.format(RECEIVED),
          "%s %s".formatted(confirmed.protocolId(), confirmed.protocolVersion())
        )
      ),
      Optional.empty()
    );
  }
}
