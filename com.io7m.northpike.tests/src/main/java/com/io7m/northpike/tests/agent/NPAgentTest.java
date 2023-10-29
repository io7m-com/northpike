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
import com.io7m.northpike.agent.internal.NPAgent;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicEd448Type;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;
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
import java.util.List;
import java.util.Locale;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

@Timeout(value = 5L, unit = TimeUnit.SECONDS)
public final class NPAgentTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentTest.class);

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
  private NPAgentConfiguration configuration;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.keyPair =
      new NPAgentKeyPairFactoryEd448()
        .generateKeyPair();
    this.key =
      this.keyPair.publicKey();

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
        new NPAgentLocalDescription(
          NPAgentLocalName.of("a"),
          this.keyPair
        ),
        new NPAgentServerDescription(
          new NPAgentServerID(UUID.randomUUID()),
          this.socket.getInetAddress().getHostName(),
          0x4e50,
          false,
          1_000_000
        )
      );
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.socket.close();
    this.serverCloseLatch.await(10L, TimeUnit.SECONDS);
  }

  /**
   * The login process works.
   *
   * @throws Exception On errors
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testLogin()
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

        this.doVersionNegotiation(inputStream, outputStream);

        final var received1 =
          (NPACommandCLogin) NPA1_MESSAGES.readLengthPrefixed(
            this.strings,
            1_000_000,
            inputStream
          );
        LOG.debug("{}", received1);

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          NPAResponseLoginChallenge.createCorrelated(
            received1,
            NPAgentLoginChallenge.generate()
          ));

        final var received2 =
          (NPACommandCLoginComplete) NPA1_MESSAGES.readLengthPrefixed(
            this.strings,
            1_000_000,
            inputStream
          );
        LOG.debug("{}", received2);

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          NPAResponseOK.createCorrelated(received2)
        );

        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    try (var agent = NPAgent.open(this.strings, this.configuration)) {
      agent.start();
      Thread.sleep(1_000L);
    }
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
}
