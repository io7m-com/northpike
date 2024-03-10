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

import com.io7m.genevan.core.GenProtocolException;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolServerEndpointType;
import com.io7m.genevan.core.GenProtocolSolved;
import com.io7m.genevan.core.GenProtocolSolver;
import com.io7m.genevan.core.GenProtocolVersion;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.internal.NPAgentExceptions;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.SocketFactory;
import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.security.GeneralSecurityException;
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
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentConnectionHandlers.class);

  private static final SocketFactory SOCKETS =
    SocketFactory.getDefault();
  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private NPAgentConnectionHandlers()
  {

  }

  /**
   * Open a new connection handler.
   *
   * @param strings     The string resources
   * @param tlsContexts The TLS context service
   * @param server      The server configuration
   *
   * @return A new connection handler
   *
   * @throws NPException On errors
   */

  public static NPAgentConnectionHandlerType openConnectionHandler(
    final NPStrings strings,
    final NPTLSContextServiceType tlsContexts,
    final NPAgentServerDescription server)
    throws NPException
  {
    final var socketAddress =
      new InetSocketAddress(
        server.hostname(),
        server.port()
      );

    LOG.info(
      "Connect {} (TLS {})",
      socketAddress,
      server.tls()
    );

    try {
      final var socket =
        switch (server.tls()) {
          case final NPTLSDisabled ignored -> {
            yield SOCKETS.createSocket();
          }

          case final NPTLSEnabledExplicit enabled -> {
            yield tlsContexts.create(
                "Agent",
                enabled.keyStore(),
                enabled.trustStore()
              ).context()
              .getSocketFactory()
              .createSocket();
          }

          case final NPTLSEnabledClientAnonymous ignored -> {
            yield tlsContexts.createClientAnonymous("Agent")
              .context()
              .getSocketFactory()
              .createSocket();
          }
        };

      try {
        socket.setTcpNoDelay(true);
        socket.setPerformancePreferences(1, 2, 0);
        socket.connect(socketAddress, 10);
        return negotiateVersion(strings, server, socket);
      } catch (final IOException | NPProtocolException e) {
        socket.close();
        throw e;
      }
    } catch (final IOException e) {
      throw NPAgentExceptions.errorIO(strings, e);
    } catch (final GeneralSecurityException e) {
      throw NPAgentExceptions.errorSecurity(e);
    } catch (final NPProtocolException e) {
      throw NPAgentExceptions.errorProtocol(e);
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
    final NPStrings strings,
    final NPAgentServerDescription server,
    final Socket socket)
    throws IOException, NPAgentException, NPProtocolException
  {
    final var inputStream =
      socket.getInputStream();
    final var outputStream =
      socket.getOutputStream();

    final var available =
      readNPIMessageOfType(
        strings,
        server,
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

    NPI_MESSAGES.writeLengthPrefixed(outputStream, chosen);

    final var confirmed =
      readNPIMessageOfType(
        strings,
        server,
        inputStream,
        NPIProtocol.class
      );

    if (!chosen.equals(confirmed)) {
      throw errorServerFailedConfirmation(
        strings,
        chosen,
        confirmed
      );
    }

    return solved.clientHandler()
      .createHandler(
        strings,
        server,
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

  private static <M extends NPIMessageType> M readNPIMessageOfType(
    final NPStrings strings,
    final NPAgentServerDescription server,
    final InputStream inputStream,
    final Class<M> clazz)
    throws IOException, NPAgentException, NPProtocolException
  {
    final var message =
      NPI_MESSAGES.readLengthPrefixed(
        strings,
        server.messageSizeLimit(),
        inputStream
      );

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
