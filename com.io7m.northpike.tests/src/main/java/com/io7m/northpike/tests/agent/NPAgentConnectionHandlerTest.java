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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent.NPACommandCDisconnect;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.percentpass.extension.MinimumPassing;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ServerSocketFactory;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.UUID;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static com.io7m.northpike.agent.internal.NPAgentConnectionHandlers.openConnectionHandler;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

@Timeout(value = 5L, unit = TimeUnit.SECONDS)
public final class NPAgentConnectionHandlerTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentConnectionHandlerTest.class);

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

  @BeforeEach
  public void setup(
    final @TempDir Path dirWork,
    final @TempDir Path dirTemp)
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
        NPAWorkExecutorConfiguration.builder()
          .setWorkDirectory(dirWork)
          .setTemporaryDirectory(dirTemp)
          .setExecutorType(new RDottedName("workexec.local"))
          .build(),
        new NPAgentLocalDescription(
          NPAgentLocalName.of("x"),
          new NPAgentKeyPairFactoryEd448().generateKeyPair()
        ),
        new NPAgentServerDescription(
          new NPAgentServerID(UUID.randomUUID()),
          this.socket.getInetAddress().getHostName(),
          this.socket.getLocalPort(),
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
   * The connection fails if the server refuses the chosen version.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerRejectsVersion()
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

        final NPIProtocol received0 =
          (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
            this.strings,
            1000000,
            inputStream
          );

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

    final var ex =
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("go-away", ex.errorCode().id());
    assertEquals("GO AWAY!", ex.getMessage());
  }

  /**
   * The connection fails if the server sends back an invalid confirmation.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerWrongVersion()
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

        final NPIProtocol received0 =
          (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
            this.strings,
            1000000,
            inputStream
          );

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocol(NPA1Messages.protocolId(), 3L)
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
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-io", ex.errorCode().id());
    assertEquals("Server refused protocol version confirmation.", ex.getMessage());
  }

  /**
   * The connection fails if the server does not expose a supported version.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerNoSupportedVersion()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var outputStream =
          clientSocket.getOutputStream();

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocolsAvailable(
            List.of(
              new NPIProtocol(
                UUID.fromString("69f7dbbb-ed3e-4b8a-a885-c6397467767a"),
                99981L
              )
            )
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
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-no-supported-protocols", ex.errorCode().id());
  }

  /**
   * The connection fails if the server sends a message that's too large.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerMessageTooLarge()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var outputStream =
          clientSocket.getOutputStream();

        final var protocols = new ArrayList<NPIProtocol>();
        protocols.add(new NPIProtocol(NPA1Messages.protocolId(), 1L));

        for (int index = 0; index < 50000; ++index) {
          protocols.add(new NPIProtocol(UUID.randomUUID(), 23L));
        }

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocolsAvailable(protocols)
        );

        outputStream.flush();
        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-protocol", ex.errorCode().id());
    assertEquals("Exceeded message size limit.", ex.getMessage());
  }

  /**
   * The connection fails if the server sends nothing.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerNothing0()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);
        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-io", ex.errorCode().id());
    assertEquals("Read fewer octets than were required.", ex.getMessage());
  }

  /**
   * The connection fails if the server sends nonsense.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerInitialNonsense0()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var outputStream =
          clientSocket.getOutputStream();

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPIProtocol(UUID.randomUUID(), 23L)
        );

        outputStream.flush();
        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-protocol", ex.errorCode().id());
    assertEquals("Protocol error.", ex.getMessage());
  }

  /**
   * The connection fails if the server sends nonsense.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerInitialNonsense1()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var outputStream =
          clientSocket.getOutputStream();

        outputStream.write(0x2);
        outputStream.flush();
        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-io", ex.errorCode().id());
    assertEquals("Read fewer octets than were required.", ex.getMessage());
  }

  /**
   * The connection fails if the server sends nonsense.
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerInitialNonsense2()
  {
    this.executor.execute(() -> {
      try {
        LOG.info("Waiting for connection...");
        this.serverAcceptLatch.countDown();
        final var clientSocket = this.socket.accept();
        LOG.info("Connected: {}", clientSocket);

        final var outputStream =
          clientSocket.getOutputStream();

        outputStream.write(0);
        outputStream.write(0);
        outputStream.write(0);
        outputStream.write(1);
        outputStream.write(2);
        outputStream.flush();
        clientSocket.close();
      } catch (final Exception e) {
        LOG.error("", e);
      } finally {
        this.serverCloseLatch.countDown();
      }
    });

    this.serverAcceptLatch.countDown();

    final var ex =
      assertThrows(NPAgentException.class, () -> {
        openConnectionHandler(this.strings, this.configuration);
      });

    assertEquals("error-io", ex.errorCode().id());
  }

  /**
   * The connection succeeds if the server confirms the chosen version.
   *
   * @throws Exception On errors
   */

  @MinimumPassing(executionCount = 5, passMinimum = 3)
  public void testServerSuccess0()
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

        final NPIProtocol received0 =
          (NPIProtocol) NPI_MESSAGES.readLengthPrefixed(
            this.strings, 1000000, inputStream);

        NPI_MESSAGES.writeLengthPrefixed(
          outputStream,
          received0
        );

        final var received1 =
          (NPACommandCEnvironmentInfo)
            NPA1_MESSAGES.readLengthPrefixed(
              this.strings, 1000000, inputStream);

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseOK(
            UUID.randomUUID(),
            received1.messageID()
          )
        );

        final var received2 =
          (NPACommandCDisconnect)
            NPA1_MESSAGES.readLengthPrefixed(
              this.strings, 1000000, inputStream);

        NPA1_MESSAGES.writeLengthPrefixed(
          outputStream,
          new NPAResponseOK(
            UUID.randomUUID(),
            received2.messageID()
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

    try (var connection = openConnectionHandler(this.strings, this.configuration)) {
      connection.send(NPACommandCEnvironmentInfo.of());
      connection.send(NPACommandCDisconnect.of());
    }
  }
}
