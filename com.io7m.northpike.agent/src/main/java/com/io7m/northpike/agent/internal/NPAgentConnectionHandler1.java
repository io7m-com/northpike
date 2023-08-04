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

import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Objects;
import java.util.Optional;

/**
 * The agent handler for protocol version 1.
 */

public final class NPAgentConnectionHandler1
  extends NPAgentConnectionHandlerAbstract
{
  private static final NPA1Messages MESSAGES =
    new NPA1Messages();

  private final Socket socket;
  private final OutputStream output;
  private final InputStream input;

  NPAgentConnectionHandler1(
    final NPAgentConfiguration configuration,
    final Socket inSocket,
    final InputStream inInputStream,
    final OutputStream inOutputStream)
  {
    super(configuration);

    this.socket =
      Objects.requireNonNull(inSocket, "socket");
    this.input =
      Objects.requireNonNull(inInputStream, "inOutput");
    this.output =
      Objects.requireNonNull(inOutputStream, "inInput");
  }

  @Override
  public void send(
    final NPAMessageType message)
    throws NPAgentException
  {
    try {
      MESSAGES.writeLengthPrefixed(this.output, message);
    } catch (final IOException e) {
      throw NPAgentExceptions.errorIO(this.strings(), e);
    } catch (final NPProtocolException e) {
      throw NPAgentExceptions.errorProtocol(e);
    }
  }

  @Override
  public Optional<NPAMessageType> receive()
    throws NPAgentException
  {
    try {
      if (this.input.available() <= 4) {
        return Optional.empty();
      }

      final var sizeBytes = this.input.readNBytes(4);
      if (sizeBytes.length != 4) {
        throw NPAgentExceptions.errorShortRead(
          this.strings(),
          4,
          sizeBytes.length
        );
      }

      final var sizeData = ByteBuffer.wrap(sizeBytes);
      sizeData.order(ByteOrder.BIG_ENDIAN);

      final var messageSize = sizeData.getInt(0);
      if (messageSize > this.configuration().messageSizeLimit()) {
        throw NPAgentExceptions.errorTooLarge(
          this.strings(),
          messageSize,
          this.configuration().messageSizeLimit()
        );
      }

      final var messageData =
        this.input.readNBytes(messageSize);

      return Optional.of(MESSAGES.parse(messageData));
    } catch (final NPProtocolException e) {
      throw NPAgentExceptions.errorProtocol(e);
    } catch (final IOException e) {
      throw NPAgentExceptions.errorIO(this.strings(), e);
    }
  }

  @Override
  public void close()
    throws NPAgentException
  {
    try {
      this.socket.close();
    } catch (final IOException e) {
      throw NPAgentExceptions.errorIO(this.strings(), e);
    }
  }
}
