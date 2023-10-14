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


package com.io7m.northpike.shell.internal;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPValidityException;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see NPAgentKeyPublicType
 */

public final class NPAgentPublicKeyConverter
  implements QValueConverterType<NPAgentKeyPublicType>
{
  /**
   * @see NPAgentKeyPublicType
   */

  public NPAgentPublicKeyConverter()
  {

  }

  @Override
  public NPAgentKeyPublicType convertFromString(
    final String text)
  {
    final var segments = text.split(":");
    if (segments.length != 2) {
      throw new NPValidityException("Unparseable public key.");
    }

    return switch (segments[0]) {
      case NPAgentKeyPairEd448Type.ALGORITHM_NAME -> {
        try {
          yield new NPAgentKeyPairFactoryEd448()
            .parsePublicKeyFromText(segments[1]);
        } catch (final NPException e) {
          throw new IllegalArgumentException(e);
        }
      }
      default -> {
        throw new IllegalArgumentException("Unrecognized key algorithm.");
      }
    };
  }

  @Override
  public String convertToString(
    final NPAgentKeyPublicType value)
  {
    return "%s:%s".formatted(value.algorithm(), value.asText());
  }

  @Override
  public NPAgentKeyPublicType exampleValue()
  {
    return new NPAgentKeyPairFactoryEd448()
      .generateKeyPair()
      .publicKey();
  }

  @Override
  public String syntax()
  {
    return "<algorithm> : [a-f0-9]+";
  }

  @Override
  public Class<NPAgentKeyPublicType> convertedClass()
  {
    return NPAgentKeyPublicType.class;
  }
}
