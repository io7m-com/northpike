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

import com.io7m.genevan.core.GenProtocolException;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolServerEndpointType;
import com.io7m.genevan.core.GenProtocolSolved;
import com.io7m.genevan.core.GenProtocolSolver;
import com.io7m.genevan.core.GenProtocolVersion;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientConfiguration;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.protocol.agent_console.cb.NPACMessages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.net.Socket;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.agent.console_client.internal.NPAConsoleExceptions.errorUnexpectedMessage;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_SERVER_FAILED_PROTOCOL_CONFIRMATION;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;


/**
 * Functions to create connection handlers.
 */

public final class NPAConsoleConnectionHandlers
{
  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private NPAConsoleConnectionHandlers()
  {

  }

  /**
   * Open a new connection handler.
   *
   * @param configuration The configuration
   *
   * @return A new connection handler
   *
   * @throws NPAConsoleClientException On errors
   */

  public static NPAConsoleConnectionHandlerType openConnectionHandler(
    final NPAConsoleConnectionParameters configuration)
    throws NPAConsoleClientException
  {
    try {
      final var socket =
        new Socket();
      final var socketAddress =
        configuration.address();

      try {
        socket.setTcpNoDelay(true);
        socket.setPerformancePreferences(1, 2, 0);
        socket.connect(socketAddress, 10);
        return negotiateVersion(configuration.configuration(), socket);
      } catch (final IOException | NPProtocolException e) {
        socket.close();
        throw e;
      }
    } catch (final IOException e) {
      throw NPAConsoleExceptions.errorIO(
        configuration.configuration().strings(),
        e);
    } catch (final NPProtocolException e) {
      throw NPAConsoleExceptions.errorProtocol(e);
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

  private static NPAConsoleConnectionHandlerType negotiateVersion(
    final NPAConsoleClientConfiguration configuration,
    final Socket socket)
    throws IOException, NPAConsoleClientException, NPProtocolException
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

    final GenProtocolSolved<NPAConsoleConnectionHandlerFactoryType, NPServerEndpoint> solved =
      solveVersion(available);

    final var solvedEndpoint =
      solved.serverEndpoint();

    final var chosen =
      new NPIProtocol(
        UUID.fromString(solvedEndpoint.supported.identifier()),
        solvedEndpoint.supported.version().versionMajor().longValue()
      );

    NPI_MESSAGES.writeLengthPrefixed(outputStream, chosen);

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

  private static GenProtocolSolved<NPAConsoleConnectionHandlerFactoryType, NPServerEndpoint>
  solveVersion(
    final NPIProtocolsAvailable available)
    throws NPAConsoleClientException
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
      List.of(new NPAConsoleConnectionHandlerFactory1());

    final var solver =
      GenProtocolSolver.<NPAConsoleConnectionHandlerFactoryType, NPServerEndpoint>
        create(Locale.ROOT);

    final GenProtocolSolved<NPAConsoleConnectionHandlerFactoryType, NPServerEndpoint> solved;
    try {
      solved = solver.solve(
        supportedByServer,
        supportedByClient,
        List.of(NPACMessages.protocolId().toString())
      );
    } catch (final GenProtocolException e) {
      throw new NPAConsoleClientException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorNoSupportedProtocols(),
        Map.of(),
        Optional.empty()
      );
    }
    return solved;
  }

  private static <M extends NPIMessageType> M readNPIMessageOfType(
    final NPAConsoleClientConfiguration configuration,
    final InputStream inputStream,
    final Class<M> clazz)
    throws IOException, NPAConsoleClientException, NPProtocolException
  {
    final var strings =
      configuration.strings();
    final var message =
      NPI_MESSAGES.readLengthPrefixed(
        strings,
        Integer.MAX_VALUE,
        inputStream
      );

    if (message instanceof final NPIError error) {
      throw new NPAConsoleClientException(
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

  private static NPAConsoleClientException errorServerFailedConfirmation(
    final NPStrings strings,
    final NPIProtocol expected,
    final NPIProtocol confirmed)
  {
    return new NPAConsoleClientException(
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
