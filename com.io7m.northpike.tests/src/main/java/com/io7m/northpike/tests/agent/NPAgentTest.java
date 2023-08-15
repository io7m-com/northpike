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

import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentStatus;
import com.io7m.northpike.agent.internal.NPAgent;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPKey;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ServerSocketFactory;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.time.OffsetDateTime;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTED;
import static com.io7m.northpike.agent.api.NPAgentStatus.CONNECTING;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

@Timeout(value = 5L, unit = TimeUnit.SECONDS)
public final class NPAgentTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentTest.class);

  private static final NPKey KEY =
    NPKey.parse(
      "52864e79eb41c62842e31cad2382584b18621c2a699d80844e92292882795b8e");

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private static final NPA1Messages NPA1_MESSAGES =
    new NPA1Messages();

  private ServerSocket socket;
  private NPStrings strings;
  private ExecutorService executor;
  private CountDownLatch serverCloseLatch;
  private CountDownLatch serverAcceptLatch;
  private NPAgentConfiguration configuration;
  private LinkedBlockingQueue<NPAMessageType> received;

  private static void checkStatuses(
    final HashSet<NPAgentStatus> statuses,
    final Set<NPAgentStatus> requiredStatuses,
    final Set<NPAgentStatus> refusedStatuses)
  {
    for (final var status : NPAgentStatus.values()) {
      if (requiredStatuses.contains(status)) {
        assertTrue(
          statuses.contains(status),
          "Status set %s must contain %s".formatted(statuses, status)
        );
        continue;
      }
      if (refusedStatuses.contains(status)) {
        assertFalse(
          statuses.contains(status),
          "Status set %s must not contain %s".formatted(statuses, status)
        );
      }
    }
  }

  @BeforeEach
  public void setup()
    throws Exception
  {
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

    this.configuration =
      new NPAgentConfiguration(
        this.strings,
        this.socket.getInetAddress(),
        this.socket.getLocalPort(),
        false,
        KEY,
        1_000_000
      );

    this.received =
      new LinkedBlockingQueue<NPAMessageType>();
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.socket.close();
    this.serverCloseLatch.await(10L, TimeUnit.SECONDS);
  }

  /**
   * The connection fails if the server refuses the chosen version.
   *
   * @throws Exception On errors
   */

  @Test
  public void testServerRejectsVersion()
    throws Exception
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

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocolsAvailable(
            List.of(
              new NPIProtocol(NPA1Messages.protocolId(), 1L)
            )
          )
        );

        final var received0 =
          (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIError(
            new NPErrorCode("go-away"),
            "GO AWAY!"
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

    final var statuses = new HashSet<NPAgentStatus>();
    try (var agent = NPAgent.open(this.configuration)) {
      agent.status()
        .subscribe((oldValue, newValue) -> statuses.add(newValue));

      agent.start();
      Thread.sleep(2000L);
      agent.stop();
    }

    final var requiredStatuses =
      Set.of(CONNECTING);
    final var refusedStatuses =
      Set.of(CONNECTED);

    checkStatuses(statuses, requiredStatuses, refusedStatuses);
  }

  /**
   * The agent correctly responds to latency check requests.
   *
   * @throws Exception On errors
   */

  @Test
  public void testAgentLatencyCheck()
    throws Exception
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

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocolsAvailable(
            List.of(
              new NPIProtocol(NPA1Messages.protocolId(), 1L)
            )
          )
        );

        final var received0 =
          (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);

        NPI_MESSAGES.writeLengthPrefixed(outputStream, received0);

        final var received1 =
          (NPACommandCLogin) NPA1_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);
        this.received.add(received1);

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseOK(UUID.randomUUID(), received1.messageID())
        );

        final var received2 =
          (NPACommandCEnvironmentInfo) NPA1_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);
        this.received.add(received2);

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseOK(UUID.randomUUID(), received2.messageID())
        );

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPACommandSLatencyCheck(
            UUID.randomUUID(),
            OffsetDateTime.now()
          )
        );

        final var received3 =
          (NPAResponseLatencyCheck) NPA1_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);
        this.received.add(received3);

        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var statuses = new HashSet<NPAgentStatus>();
    try (var agent = NPAgent.open(this.configuration)) {
      agent.status()
        .subscribe((oldValue, newValue) -> statuses.add(newValue));

      agent.start();
      Thread.sleep(2000L);
      agent.stop();
    }

    assertInstanceOf(NPACommandCLogin.class, this.received.poll());
    assertInstanceOf(NPACommandCEnvironmentInfo.class, this.received.poll());
    assertInstanceOf(NPAResponseLatencyCheck.class, this.received.poll());
  }
}
