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

import java.io.IOException;
import java.io.OutputStream;
import java.util.Properties;

/**
 * <p>The base type of key pairs.</p>
 *
 * <p>A key pair has a unique ID, for organizational purposes. The ID is loosely
 * defined as a unique but relatively short value calculated from the public
 * key of the key pair. In the case of Ed448, for example, the key ID is simply
 * the 57 bytes of the public key as the key is already small enough not to be
 * unwieldy. If RSA keys were supported, the ID would likely be the SHA256 hash
 * of the public key integers.</p>
 */

public sealed interface NPAgentKeyPairType
  permits NPAgentKeyPairEd448Type
{
  /**
   * @return The public key
   */

  NPAgentKeyPublicType publicKey();

  /**
   * @return The private key
   */

  NPAgentKeyPrivateType privateKey();

  /**
   * @return The key ID (of the public key)
   */

  default NPAgentKeyID id()
  {
    return this.publicKey().id();
  }

  /**
   * Encode this key pair as a set of Java properties.
   *
   * @return The properties
   */

  Properties toProperties();

  /**
   * Encode this key pair to the given stream as a set of properties.
   *
   * @param outputStream The output stream
   *
   * @throws IOException On I/O errors
   */

  default void encodeToStream(
    final OutputStream outputStream)
    throws IOException
  {
    final var properties = this.toProperties();
    properties.store(outputStream, "");
  }

  /**
   * Sign the given data using this key pair.
   *
   * @param data The data
   *
   * @return The signature
   *
   * @see NPAgentKeyPrivateType#signData(byte[])
   */

  default byte[] signData(
    final byte[] data)
    throws NPException
  {
    return this.privateKey()
      .signData(data);
  }

  /**
   * Verify the given signed data using this key pair.
   *
   * @param signed The signed data
   *
   * @return {@code true} if verification succeeds
   *
   * @see NPAgentKeyPublicType#verifyData(NPSignedData)
   */

  default boolean verifyData(
    final NPSignedData signed)
    throws NPException
  {
    return this.publicKey()
      .verifyData(signed);
  }

  /**
   * @return The algorithm name
   *
   * @see "https://docs.oracle.com/en/java/javase/21/docs/specs/security/standard-names.html"
   */

  String algorithm();
}
