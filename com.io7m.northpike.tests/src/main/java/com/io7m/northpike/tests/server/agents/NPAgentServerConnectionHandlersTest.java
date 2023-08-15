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


package com.io7m.northpike.tests.server.agents;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.cb.NPIMessages;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.agents.NPAgentServerConnection;
import com.io7m.northpike.strings.NPStrings;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.net.ServerSocketFactory;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Locale;
import java.util.UUID;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNoSupportedProtocols;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPAgentServerConnectionHandlersTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentServerConnectionHandlersTest.class);

  private static final NPIMessages NPI_MESSAGES =
    new NPIMessages();

  private static final NPIProtocol NPA_1 =
    new NPIProtocol(NPA1Messages.protocolId(), 1L);

  private static final NPIProtocol NONSENSE =
    new NPIProtocol(
      UUID.fromString("7bc57762-aacf-46cb-ae61-66b564ea7e6c"),
      1L
    );

  private static final int SIZE_LIMIT = 1000000;

  private ExecutorService executor;
  private ServerSocket serverSocket;
  private CloseableCollectionType<ClosingResourceFailedException> resources;
  private AtomicBoolean failed;
  private NPStrings strings;

  @BeforeEach
  public void setup()
    throws Exception
  {
    this.failed =
      new AtomicBoolean(false);
    this.resources =
      CloseableCollection.create();

    this.strings = NPStrings.create(Locale.ROOT);

    this.executor = Executors.newCachedThreadPool();
    this.resources.add(this.executor::shutdown);

    this.serverSocket =
      this.resources.add(
        ServerSocketFactory.getDefault()
          .createServerSocket(20049, 100, InetAddress.getLocalHost())
      );
  }

  @AfterEach
  public void tearDown()
    throws Exception
  {
    this.resources.close();
    this.executor.awaitTermination(5L, TimeUnit.SECONDS);
  }

  /**
   * Unsupported protocols produce the correct errors.
   *
   * @throws Exception On errors
   */

  @Test
  public void testUnsupportedProtocolRequested()
    throws Exception
  {
    this.executor.execute(() -> {
      try {
        try (var socket = new Socket(InetAddress.getLocalHost(), 20049)) {
          final var input =
            socket.getInputStream();
          final var output =
            socket.getOutputStream();

          NPI_MESSAGES.readLengthPrefixed(this.strings, SIZE_LIMIT, input);
          NPI_MESSAGES.writeLengthPrefixed(output, NONSENSE);
          NPI_MESSAGES.readLengthPrefixed(this.strings, SIZE_LIMIT, input);
        }
      } catch (final Exception e) {
        LOG.error("", e);
        this.failed.set(true);
      }
    });

    final var socket =
      this.resources.add(this.serverSocket.accept());

    final var ex =
      assertThrows(NPServerException.class, () -> {
        NPAgentServerConnection.open(this.strings, SIZE_LIMIT, socket);
      });

    assertEquals(errorNoSupportedProtocols(), ex.errorCode());
    assertFalse(this.failed.get());
  }

  /**
   * Sending something that is not a protocol causes errors.
   *
   * @throws Exception On errors
   */

  @Test
  public void testProtocolMisuse0()
    throws Exception
  {
    this.executor.execute(() -> {
      try {
        try (var socket = new Socket(InetAddress.getLocalHost(), 20049)) {
          final var input =
            socket.getInputStream();
          final var output =
            socket.getOutputStream();

          NPI_MESSAGES.readLengthPrefixed(this.strings, SIZE_LIMIT, input);
          NPI_MESSAGES.writeLengthPrefixed(
            output, new NPIError(errorIo(), "What?"));
          NPI_MESSAGES.readLengthPrefixed(this.strings, SIZE_LIMIT, input);
        }
      } catch (final Exception e) {
        LOG.error("", e);
        this.failed.set(true);
      }
    });

    final var socket =
      this.resources.add(this.serverSocket.accept());

    final var ex =
      assertThrows(NPServerException.class, () -> {
        NPAgentServerConnection.open(this.strings, SIZE_LIMIT, socket);
      });

    assertEquals(errorProtocol(), ex.errorCode());
    assertFalse(this.failed.get());
  }

  /**
   * Sending something that is not a protocol causes errors.
   *
   * @throws Exception On errors
   */

  @Test
  public void testProtocolMisuse1()
    throws Exception
  {
    this.executor.execute(() -> {
      try {
        try (var socket = new Socket(InetAddress.getLocalHost(), 20049)) {
          final var input =
            socket.getInputStream();
          final var output =
            socket.getOutputStream();

          NPI_MESSAGES.readLengthPrefixed(this.strings, SIZE_LIMIT, input);

          final byte[] data = new byte[8];
          data[0] = (byte) 0;
          data[1] = (byte) 0;
          data[2] = (byte) 0;
          data[3] = (byte) 4;
          data[4] = (byte) 0xa0;
          data[5] = (byte) 0xb0;
          data[6] = (byte) 0xc0;
          data[7] = (byte) 0xd0;
          output.write(data);
        }
      } catch (final Exception e) {
        LOG.error("", e);
        this.failed.set(true);
      }
    });

    final var socket =
      this.resources.add(this.serverSocket.accept());

    final var ex =
      assertThrows(NPProtocolException.class, () -> {
        NPAgentServerConnection.open(this.strings, SIZE_LIMIT, socket);
      });

    assertEquals(errorIo(), ex.errorCode());
    assertFalse(this.failed.get());
  }

  /**
   * Short reads produce errors.
   *
   * @throws Exception On errors
   */

  @Test
  public void testShortRead0()
    throws Exception
  {
    this.executor.execute(() -> {
      try {
        try (var socket = new Socket(InetAddress.getLocalHost(), 20049)) {
          // Close immediately without writing anything
        }
      } catch (final Exception e) {
        LOG.error("", e);
        this.failed.set(true);
      }
    });

    final var socket =
      this.resources.add(this.serverSocket.accept());

    final var ex =
      assertThrows(NPProtocolException.class, () -> {
        NPAgentServerConnection.open(this.strings, SIZE_LIMIT, socket);
      });

    assertEquals(errorIo(), ex.errorCode());
    assertFalse(this.failed.get());
  }

  /**
   * Exceeding the size limit is an error.
   *
   * @throws Exception On errors
   */

  @Test
  public void testSizeExceeded()
    throws Exception
  {
    this.executor.execute(() -> {
      try {
        try (var socket = new Socket(InetAddress.getLocalHost(), 20049)) {
          final var input =
            socket.getInputStream();
          final var output =
            socket.getOutputStream();

          NPI_MESSAGES.readLengthPrefixed(this.strings, SIZE_LIMIT, input);

          final byte[] data = new byte[8];
          data[0] = (byte) 0x70;
          data[1] = (byte) 0;
          data[2] = (byte) 0;
          data[3] = (byte) 0;
          data[4] = (byte) 0xa0;
          data[5] = (byte) 0xb0;
          data[6] = (byte) 0xc0;
          data[7] = (byte) 0xd0;
          output.write(data);
        }
      } catch (final Exception e) {
        LOG.error("", e);
        this.failed.set(true);
      }
    });

    final var socket =
      this.resources.add(this.serverSocket.accept());

    final var ex =
      assertThrows(NPProtocolException.class, () -> {
        NPAgentServerConnection.open(this.strings, SIZE_LIMIT, socket);
      });

    assertEquals(errorProtocol(), ex.errorCode());
    assertFalse(this.failed.get());
  }
}
