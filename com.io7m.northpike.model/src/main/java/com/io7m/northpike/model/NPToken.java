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

import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.HexFormat;
import java.util.Objects;
import java.util.regex.Pattern;

/**
 * A unique token.
 *
 * @param value The token value
 */

public record NPToken(String value)
  implements Comparable<NPToken>
{
  private static final Pattern VALID_VALUE =
    Pattern.compile("[a-f0-9]{64}");

  /**
   * A unique token.
   *
   * @param value The token value
   */

  public NPToken
  {
    Objects.requireNonNull(value, "value");

    if (!VALID_VALUE.matcher(value).matches()) {
      throw new NPValidityException(
        "Token must match the pattern %s".formatted(VALID_VALUE)
      );
    }
  }

  /**
   * Generate a random token.
   *
   * @return The token
   *
   * @throws NoSuchAlgorithmException If no secure RNG is available
   */

  public static NPToken generate()
    throws NoSuchAlgorithmException
  {
    return generate(SecureRandom.getInstanceStrong());
  }

  /**
   * Generate a random token.
   *
   * @param random The RNG
   *
   * @return The token
   */

  public static NPToken generate(
    final SecureRandom random)
  {
    final var bytes = new byte[32];
    random.nextBytes(bytes);
    return of(bytes);
  }

  /**
   * Construct a token from the given bytes.
   *
   * @param bytes An array of 32 bytes
   *
   * @return The token
   */

  public static NPToken of(
    final byte[] bytes)
  {
    return new NPToken(
      HexFormat.of()
        .withLowerCase()
        .formatHex(bytes)
    );
  }

  @Override
  public String toString()
  {
    return this.value;
  }

  @Override
  public int compareTo(
    final NPToken other)
  {
    return this.value.compareTo(other.value);
  }
}
