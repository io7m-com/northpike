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


package com.io7m.northpike.model.agents;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPSignedData;

import java.util.HexFormat;

/**
 * The base type of public keys.
 */

public sealed interface NPAgentKeyPublicType
  permits NPAgentKeyPublicEd448Type
{
  /**
   * @return The key ID
   */

  NPAgentKeyID id();

  /**
   * Verify the given signed data against this key.
   *
   * @param signed The signed data
   *
   * @return {@code true} if verification succeeded
   */

  boolean verifyData(
    NPSignedData signed)
    throws NPException;

  /**
   * @return The raw key as hexadecimal ASCII-encoded bytes
   */

  default String asText()
  {
    return HexFormat.of().formatHex(this.asBytes());
  }

  /**
   * @return The key algorithm name
   */

  String algorithm();

  /**
   * @return The raw key as bytes
   */

  byte[] asBytes();
}
