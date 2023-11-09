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
import com.io7m.northpike.model.NPStandardErrorCodes;

import java.io.IOException;
import java.io.InputStream;
import java.util.HexFormat;
import java.util.Map;
import java.util.Optional;
import java.util.Properties;

/**
 * A factory of key pairs.
 */

public sealed interface NPAgentKeyPairFactoryType
  permits NPAgentKeyPairFactoryEd448Type
{
  /**
   * Generate a new key pair.
   *
   * @return A new key pair
   *
   * @throws NPException On errors
   */

  NPAgentKeyPairType generateKeyPair()
    throws NPException;

  /**
   * Parse a key pair
   *
   * @param properties The properties containing the encoded key
   *
   * @return A parsed key pair
   *
   * @throws NPException On errors
   * @see NPAgentKeyPairType#toProperties()
   */

  NPAgentKeyPairType parseFromProperties(
    Properties properties)
    throws NPException;

  /**
   * Parse a key pair
   *
   * @param publicKey  The encoded public key
   * @param privateKey The encoded private key
   *
   * @return A parsed key pair
   *
   * @throws NPException On errors
   * @see NPAgentKeyPairType#toProperties()
   */

  NPAgentKeyPairType parseFromText(
    String publicKey,
    String privateKey)
    throws NPException;

  /**
   * Parse a public key from the given text.
   *
   * @param publicKey The encoded public key
   *
   * @return A parsed public key
   *
   * @throws NPException On errors
   * @see NPAgentKeyPairType#toProperties()
   */

  default NPAgentKeyPublicType parsePublicKeyFromText(
    final String publicKey)
    throws NPException
  {
    return this.parsePublicKeyFromBytes(HexFormat.of().parseHex(publicKey));
  }

  /**
   * Parse a public key from the given text.
   *
   * @param publicKey The encoded public key
   *
   * @return A parsed public key
   *
   * @throws NPException On errors
   * @see NPAgentKeyPairType#toProperties()
   */

  NPAgentKeyPublicType parsePublicKeyFromBytes(
    byte[] publicKey)
    throws NPException;

  /**
   * Parse a key pair from the given stream. The stream is expected to
   * contain {@link Properties} data describing the key pair.
   *
   * @param stream The input stream
   *
   * @return A parsed key pair
   *
   * @throws NPException On errors
   * @see NPAgentKeyPairType#toProperties()
   */

  default NPAgentKeyPairType parseFromStream(
    final InputStream stream)
    throws NPException
  {
    try {
      final var properties = new Properties();
      properties.load(stream);
      return this.parseFromProperties(properties);
    } catch (final IOException e) {
      throw new NPException(
        e.getMessage(),
        e,
        NPStandardErrorCodes.errorIo(),
        Map.of(),
        Optional.empty()
      );
    }
  }
}
