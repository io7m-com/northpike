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

package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.connections.NPMessageHandlerType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.strings.NPStrings;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Objects;
import java.util.Optional;

/**
 * The server handler for protocol version 1.
 */

public final class NPAgentServerConnectionHandler1
  implements NPMessageHandlerType<NPAMessageType>
{
  private static final NPA1Messages MESSAGES =
    new NPA1Messages();

  private final OutputStream output;
  private final int messageSizeLimit;
  private final NPStrings strings;
  private final InputStream input;

  NPAgentServerConnectionHandler1(
    final int inMessageSizeLimit,
    final NPStrings inStrings,
    final InputStream inInputStream,
    final OutputStream inOutputStream)
  {
    this.messageSizeLimit =
      inMessageSizeLimit;
    this.strings =
      Objects.requireNonNull(inStrings, "inStrings");
    this.input =
      Objects.requireNonNull(inInputStream, "inOutput");
    this.output =
      Objects.requireNonNull(inOutputStream, "inInput");
  }

  @Override
  public Optional<NPAMessageType> receive()
    throws NPServerException
  {
    try {
      final var available = this.input.available();
      if (available <= 4) {
        return Optional.empty();
      }

      final var sizeBytes = this.input.readNBytes(4);
      if (sizeBytes.length != 4) {
        throw NPServerExceptions.errorShortRead(
          this.strings,
          4,
          sizeBytes.length
        );
      }

      final var sizeData = ByteBuffer.wrap(sizeBytes);
      sizeData.order(ByteOrder.BIG_ENDIAN);

      final var messageSize = sizeData.getInt(0);
      if (messageSize > this.messageSizeLimit) {
        throw NPServerExceptions.errorTooLarge(
          this.strings,
          messageSize,
          this.messageSizeLimit
        );
      }

      final var messageData =
        this.input.readNBytes(messageSize);

      return Optional.of(MESSAGES.parse(messageData));
    } catch (final NPProtocolException e) {
      throw NPServerExceptions.errorProtocol(e);
    } catch (final IOException e) {
      throw NPServerExceptions.errorIO(this.strings, e);
    }
  }

  @Override
  public void send(
    final NPAMessageType message)
    throws NPServerException
  {
    try {
      MESSAGES.writeLengthPrefixed(this.output, message);
    } catch (final NPProtocolException e) {
      throw NPServerExceptions.errorProtocol(e);
    } catch (final IOException e) {
      throw NPServerExceptions.errorIO(this.strings, e);
    }
  }

  @Override
  public void close()
  {

  }
}
