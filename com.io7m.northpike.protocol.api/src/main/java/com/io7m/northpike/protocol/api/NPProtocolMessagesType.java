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


package com.io7m.northpike.protocol.api;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.function.Function;

/**
 * The interface exposed by protocol message handlers.
 *
 * @param <T> The type of protocol messages
 */

public interface NPProtocolMessagesType<T extends NPProtocolMessageType>
{
  /**
   * Parse a message from the given bytes.
   *
   * @param data The bytes
   *
   * @return A parsed message
   *
   * @throws NPProtocolException If parsing fails
   */

  T parse(byte[] data)
    throws NPProtocolException;

  /**
   * A convenience method to parse a message from a length-prefixed byte array.
   * The first four bytes of the array denote a big-endian unsigned 32-bit
   * integer length, and the bytes that constitute the message data follow
   * directly.
   *
   * @param data       The byte array
   * @param exceptions A function that produces an exception message
   *
   * @return A parsed message
   *
   * @throws NPProtocolException On errors
   */

  default T parseLengthPrefixed(
    final byte[] data,
    final Function<byte[], NPProtocolException> exceptions)
    throws NPProtocolException
  {
    if (data.length < 4) {
      throw exceptions.apply(data);
    }

    final var dataBuffer = ByteBuffer.wrap(data);
    dataBuffer.order(ByteOrder.BIG_ENDIAN);

    final var length = dataBuffer.getInt(0);
    if ((data.length - 4) < length) {
      throw exceptions.apply(data);
    }

    final var dataCopy = new byte[length];
    System.arraycopy(data, 4, dataCopy, 0, length);
    return this.parse(dataCopy);
  }

  /**
   * A convenience method to read a message from an input stream.
   * The first four bytes of the stream denote a big-endian unsigned 32-bit
   * integer length, and the bytes that constitute the message data follow
   * directly.
   *
   * @param stream The input stream
   *
   * @return A parsed message
   *
   * @throws NPProtocolException On errors
   * @throws IOException         On errors
   */

  default T readLengthPrefixed(
    final InputStream stream)
    throws NPProtocolException, IOException
  {
    final var size = stream.readNBytes(4);
    final var sizeBuffer = ByteBuffer.wrap(size);
    sizeBuffer.order(ByteOrder.BIG_ENDIAN);
    final var length = sizeBuffer.getInt(0);
    return this.parse(stream.readNBytes(length));
  }

  /**
   * Serialize the given message to a byte array.
   *
   * @param message The message
   *
   * @return The serialized message as a byte array
   *
   * @throws NPProtocolException If serialization fails
   */

  byte[] serialize(T message)
    throws NPProtocolException;

  /**
   * Serialize the given message to a byte array, prefixed with the length
   * of the data as a big-endian unsigned 32-bit integer.
   *
   * @param message The message
   *
   * @return The size plus the data
   *
   * @throws NPProtocolException On errors
   */

  default byte[] serializeLengthPrefixed(
    final T message)
    throws NPProtocolException
  {
    final var data = this.serialize(message);
    final var dataWithSize = new byte[4 + data.length];
    System.arraycopy(data, 0, dataWithSize, 4, data.length);

    final var sizeBuffer = ByteBuffer.wrap(dataWithSize);
    sizeBuffer.order(ByteOrder.BIG_ENDIAN);
    sizeBuffer.putInt(0, data.length);
    return dataWithSize;
  }

  /**
   * Write the result of {@link #serializeLengthPrefixed(NPProtocolMessageType)}
   * to the given stream.
   *
   * @param stream  The output stream
   * @param message The message
   *
   * @throws NPProtocolException On errors
   * @throws IOException         On errors
   */

  default void writeLengthPrefixed(
    final OutputStream stream,
    final T message)
    throws NPProtocolException, IOException
  {
    stream.write(this.serializeLengthPrefixed(message));
  }
}
