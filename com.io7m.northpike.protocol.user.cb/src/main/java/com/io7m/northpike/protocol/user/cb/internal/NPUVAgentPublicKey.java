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

package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBByteArray;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1PublicKey;

import java.nio.ByteBuffer;

/**
 * A validator.
 */

public enum NPUVAgentPublicKey
  implements NPProtocolMessageValidatorType<NPAgentKeyPublicType, NPU1PublicKey>
{
  /**
   * A validator.
   */

  PUBLIC_KEY;

  private static final NPAgentKeyPairFactoryEd448 ED_448 =
    new NPAgentKeyPairFactoryEd448();

  @Override
  public NPU1PublicKey convertToWire(
    final NPAgentKeyPublicType message)
  {
    if (message instanceof final NPAgentKeyPublicEd448Type ed448) {
      return new NPU1PublicKey.Ed448(
        new CBByteArray(ByteBuffer.wrap(message.asBytes()))
      );
    }

    throw new IllegalStateException(
      "Unrecognized public key type: %s".formatted(message)
    );
  }

  @Override
  public NPAgentKeyPublicType convertFromWire(
    final NPU1PublicKey message)
    throws NPProtocolException
  {
    if (message instanceof final NPU1PublicKey.Ed448 ed448) {
      try {
        return ED_448.parsePublicKeyFromBytes(
          ed448.fieldValue().value().array()
        );
      } catch (final NPException e) {
        throw new NPProtocolException(
          e.getMessage(),
          e,
          e.errorCode(),
          e.attributes(),
          e.remediatingAction()
        );
      }
    }

    throw new IllegalStateException(
      "Unrecognized public key type: %s".formatted(message)
    );
  }
}
