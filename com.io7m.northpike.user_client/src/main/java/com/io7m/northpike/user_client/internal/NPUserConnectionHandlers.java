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

import com.io7m.genevan.core.GenProtocolException;
import com.io7m.genevan.core.GenProtocolIdentifier;
import com.io7m.genevan.core.GenProtocolServerEndpointType;
import com.io7m.genevan.core.GenProtocolSolved;
import com.io7m.genevan.core.GenProtocolSolver;
import com.io7m.genevan.core.GenProtocolVersion;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.model.tls.NPTLSEnabledClientAnonymous;
import com.io7m.northpike.model.tls.NPTLSEnabledExplicit;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.protocol.user.cb.NPU1Messages;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tls.NPTLSContext;
import com.io7m.northpike.user_client.api.NPUserClientConfiguration;
import com.io7m.northpike.user_client.api.NPUserClientException;

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

import static com.io7m.northpike.strings.NPStringConstants.ERROR_SERVER_FAILED_PROTOCOL_CONFIRMATION;
import static com.io7m.northpike.strings.NPStringConstants.EXPECTED;
import static com.io7m.northpike.strings.NPStringConstants.RECEIVED;
import static com.io7m.northpike.user_client.internal.NPUserExceptions.errorUnexpectedMessage;

/**
 * Functions to create connection handlers.
 */

public final class NPUserConnectionHandlers
{
  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private NPUserConnectionHandlers()
  {

  }

  /**
   * Open a new connection handler.
   *
   * @param configuration The configuration
   *
   * @return A new connection handler
   *
   * @throws NPUserClientException On errors
   */

  public static NPUserConnectionHandlerType openConnectionHandler(
    final NPUserConnectionParameters configuration)
    throws NPUserClientException
  {
    try {
      final var socket =
        createSocket(configuration);
      final var socketAddress =
        configuration.address();

      try {
        final var socketAddressResolved =
          new InetSocketAddress(
            socketAddress.getHostName(),
            socketAddress.getPort()
          );

        socket.setTcpNoDelay(true);
        socket.setPerformancePreferences(1, 2, 0);
        socket.connect(socketAddressResolved, 10);
        return negotiateVersion(configuration.configuration(), socket);
      } catch (final IOException | NPProtocolException e) {
        socket.close();
        throw e;
      }
    } catch (final IOException e) {
      throw NPUserExceptions.errorIO(
        configuration.configuration().strings(),
        e);
    } catch (final NPProtocolException e) {
      throw NPUserExceptions.errorProtocol(e);
    }
  }

  private static Socket createSocket(
    final NPUserConnectionParameters configuration)
    throws NPUserClientException
  {
    try {
      return switch (configuration.tls()) {
        case final NPTLSDisabled ignored -> {
          yield new Socket();
        }

        case final NPTLSEnabledExplicit enabledExplicit -> {
          yield NPTLSContext.create(
              "User",
              Optional.of(enabledExplicit.keyStore()),
              Optional.of(enabledExplicit.trustStore())
            ).context()
            .getSocketFactory()
            .createSocket();
        }

        case final NPTLSEnabledClientAnonymous enabledClientAnonymous -> {
          yield NPTLSContext.create(
              "User",
              Optional.empty(),
              Optional.empty()
            ).context()
            .getSocketFactory()
            .createSocket();
        }
      };
    } catch (final IOException e) {
      throw NPUserExceptions.errorIO(
        configuration.configuration().strings(), e);
    } catch (final GeneralSecurityException e) {
      throw NPUserExceptions.errorSecurity(e);
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

  private static NPUserConnectionHandlerType negotiateVersion(
    final NPUserClientConfiguration configuration,
    final Socket socket)
    throws IOException, NPUserClientException, NPProtocolException
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

    final GenProtocolSolved<NPUserConnectionHandlerFactoryType, NPServerEndpoint> solved =
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

  private static GenProtocolSolved<NPUserConnectionHandlerFactoryType, NPServerEndpoint>
  solveVersion(
    final NPIProtocolsAvailable available)
    throws NPUserClientException
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
      List.of(new NPUserConnectionHandlerFactory1());

    final var solver =
      GenProtocolSolver.<NPUserConnectionHandlerFactoryType, NPServerEndpoint>
        create(Locale.ROOT);

    final GenProtocolSolved<NPUserConnectionHandlerFactoryType, NPServerEndpoint> solved;
    try {
      solved = solver.solve(
        supportedByServer,
        supportedByClient,
        List.of(NPU1Messages.protocolId().toString())
      );
    } catch (final GenProtocolException e) {
      throw new NPUserClientException(
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
    final NPUserClientConfiguration configuration,
    final InputStream inputStream,
    final Class<M> clazz)
    throws IOException, NPUserClientException, NPProtocolException
  {
    final var strings =
      configuration.strings();
    final var message =
      NPI_MESSAGES.readLengthPrefixed(
        strings,
        configuration.messageSizeLimit(),
        inputStream
      );

    if (message instanceof final NPIError error) {
      throw new NPUserClientException(
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

  private static NPUserClientException errorServerFailedConfirmation(
    final NPStrings strings,
    final NPIProtocol expected,
    final NPIProtocol confirmed)
  {
    return new NPUserClientException(
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
