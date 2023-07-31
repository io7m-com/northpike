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

package com.io7m.northpike.model;

import java.nio.ByteBuffer;
import java.security.SecureRandom;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.Objects;
import java.util.regex.Pattern;

/**
 * A shared secret key.
 */

public final class NPKey
{
  private static final HexFormat HEX =
    HexFormat.of();
  private static final Pattern VALID_KEY =
    Pattern.compile("[0-9a-f]{32}");
  private static final int KEY_SIZE = 32;

  private final byte[] data;

  private NPKey(
    final byte[] inData)
  {
    this.data =
      Objects.requireNonNull(inData, "data");

    if (this.data.length != KEY_SIZE) {
      throw new NPValidityException(
        "Keys must be %d octets".formatted(Integer.valueOf(KEY_SIZE))
      );
    }
  }

  /**
   * Generate a shared secret key.
   *
   * @param rng The RNG
   *
   * @return A new key
   */

  public static NPKey generate(
    final SecureRandom rng)
  {
    final var data = new byte[KEY_SIZE];
    rng.nextBytes(data);
    return new NPKey(data);
  }

  /**
   * Parse a key.
   *
   * @param text The key text
   *
   * @return A key
   */

  public static NPKey parse(
    final String text)
  {
    if (VALID_KEY.matcher(text).matches()) {
      return new NPKey(HEX.parseHex(text));
    }
    throw new NPValidityException("Invalid key.");
  }

  /**
   * Consume a key from the given byte buffer.
   *
   * @param value The byte buffer
   *
   * @return The key
   */

  public static NPKey fromByteBuffer(
    final ByteBuffer value)
  {
    final var data = new byte[KEY_SIZE];
    for (int index = 0; index < KEY_SIZE; ++index) {
      data[index] = value.get(index);
    }
    return new NPKey(data);
  }

  @Override
  public String toString()
  {
    return String.format(
      "[NPKey %02x%02x...]",
      Byte.valueOf(this.data[0]),
      Byte.valueOf(this.data[1])
    );
  }

  @Override
  public boolean equals(
    final Object o)
  {
    if (this == o) {
      return true;
    }
    if (o == null || !this.getClass().equals(o.getClass())) {
      return false;
    }
    final NPKey npKey = (NPKey) o;
    return Arrays.equals(this.data, npKey.data);
  }

  @Override
  public int hashCode()
  {
    return Arrays.hashCode(this.data);
  }

  /**
   * @return The formatted text of this key
   */

  public String format()
  {
    return HEX.formatHex(this.data);
  }

  /**
   * @return A copy of the raw bytes of this key
   */

  public byte[] data()
  {
    return this.data.clone();
  }
}
