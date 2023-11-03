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


package com.io7m.northpike.tests.agent;

import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.internal.connection.NPAgentConnection;
import com.io7m.northpike.agent.internal.connection.NPAgentConnectionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicEd448Type;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.tls.NPTLSDisabled;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryNoOp;
import com.io7m.northpike.tls.NPTLSContextService;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.percentpass.extension.MinimumPassing;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Timeout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ServerSocketFactory;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.nio.charset.StandardCharsets;
import java.time.OffsetDateTime;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

@Timeout(value = 5L, unit = TimeUnit.SECONDS)
public final class NPAgentConnectionTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentConnectionTest.class);

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();
  private static final NPA1Messages NPA1_MESSAGES =
    new NPA1Messages();

  private ExecutorService executor;
  private CountDownLatch serverAcceptLatch;
  private CountDownLatch serverCloseLatch;
  private NPStrings strings;
  private ServerSocket socket;
  private NPAgentKeyPairEd448Type keyPair;
  private NPAgentKeyPublicEd448Type key;
  private NPTLSContextServiceType tls;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.keyPair =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair();
    this.key =
      this.keyPair.publicKey();
    this.tls =
      NPTLSContextService.create(NPTelemetryNoOp.noop());

    this.executor =
      Executors.newSingleThreadExecutor();
    this.serverAcceptLatch =
      new CountDownLatch(1);
    this.serverCloseLatch =
      new CountDownLatch(1);

    this.strings =
      NPStrings.create(Locale.ROOT);

    this.socket =
      ServerSocketFactory.getDefault()
        .createServerSocket();

    this.socket.setReuseAddress(true);
    this.socket.bind(new InetSocketAddress("localhost", 0x4e50));
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.socket.close();
    this.serverCloseLatch.await(10L, TimeUnit.SECONDS);
  }

  /**
   * The connection fails if the client fails the login challenge.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testLoginChallengeFailed()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var inputStream =
          clientSocket.getInputStream();
        final var outputStream =
          clientSocket.getOutputStream();

        this.doVersionNegotiation(inputStream, outputStream);

        final var received1 =
          (NPACommandCLogin) NPA1_MESSAGES.readLengthPrefixed(
            this.strings,
            1_000_000,
            inputStream
          );

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          NPAResponseLoginChallenge.createCorrelated(
            received1,
            new NPAgentLoginChallenge(
              UUID.randomUUID(),
              "ABCD".getBytes(StandardCharsets.UTF_8)
            )
          )
        );

        final var received2 =
          (NPACommandCLoginComplete) NPA1_MESSAGES.readLengthPrefixed(
            this.strings,
            1_000_000,
            inputStream
          );

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseError(
            UUID.randomUUID(),
            received2.messageID(),
            new NPErrorCode("bad-news"),
            "BAD NEWS!",
            Map.of()
          )
        );

        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, this::openConnection);

    assertEquals("bad-news", ex.errorCode().id());
    assertEquals("BAD NEWS!", ex.getMessage());
  }

  /**
   * The connection fails if the server sends nonsense.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testLoginChallengeWrong0()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var inputStream =
          clientSocket.getInputStream();
        final var outputStream =
          clientSocket.getOutputStream();

        this.doVersionNegotiation(inputStream, outputStream);

        final var received1 =
          (NPACommandCLogin) NPA1_MESSAGES.readLengthPrefixed(
            this.strings,
            1_000_000,
            inputStream
          );

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseError(
            UUID.randomUUID(),
            received1.messageID(),
            new NPErrorCode("bad-news"),
            "BAD NEWS!",
            Map.of()
          )
        );

        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, this::openConnection);

    assertEquals("bad-news", ex.errorCode().id());
    assertEquals("BAD NEWS!", ex.getMessage());
  }

  /**
   * The connection fails if the server sends nonsense.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testLoginChallengeWrong1()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var inputStream =
          clientSocket.getInputStream();
        final var outputStream =
          clientSocket.getOutputStream();

        this.doVersionNegotiation(inputStream, outputStream);

        final var received1 =
          (NPACommandCLogin) NPA1_MESSAGES.readLengthPrefixed(
            this.strings,
            1_000_000,
            inputStream
          );

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseLatencyCheck(
            UUID.randomUUID(),
            received1.messageID(),
            OffsetDateTime.now(),
            OffsetDateTime.now()
          )
        );

        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, this::openConnection);

    assertEquals(errorProtocol(), ex.errorCode());
  }

  private void doVersionNegotiation(
    final InputStream inputStream,
    final OutputStream outputStream)
    throws NPProtocolException, IOException
  {
    NPI_MESSAGES.writeLengthPrefixed(
      outputStream,
      new NPIProtocolsAvailable(
        List.of(new NPIProtocol(NPA1Messages.protocolId(), 1L))
      )
    );

    final var received0 =
      (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
        this.strings,
        1_000_000,
        inputStream
      );

    NPI_MESSAGES.writeLengthPrefixed(
      outputStream,
      new NPIProtocol(NPA1Messages.protocolId(), 1L)
    );
  }

  private NPAgentConnectionType openConnection()
    throws NPException, InterruptedException, IOException
  {
    return NPAgentConnection.open(
      this.strings,
      this.tls,
      this.keyPair,
      new NPAgentServerDescription(
        new NPAgentServerID(UUID.randomUUID()),
        "localhost",
        this.socket.getLocalPort(),
        NPTLSDisabled.TLS_DISABLED,
        1_000_000
      )
    );
  }
}
