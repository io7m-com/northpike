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


package com.io7m.northpike.shell.commons;


import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPValidityException;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see NPToolExecutionIdentifier
 */

public final class NPToolExecutionIdentifierConverter
  implements QValueConverterType<NPToolExecutionIdentifier>
{
  /**
   * @see NPToolExecutionIdentifier
   */

  public NPToolExecutionIdentifierConverter()
  {

  }

  @Override
  public NPToolExecutionIdentifier convertFromString(
    final String text)
  {
    final var segments = text.split(":");
    if (segments.length == 2) {
      return NPToolExecutionIdentifier.of(
        segments[0],
        Long.parseUnsignedLong(segments[1])
      );
    }

    throw new NPValidityException(
      "Unparseable identifier: %s".formatted(text)
    );
  }

  @Override
  public String convertToString(
    final NPToolExecutionIdentifier value)
  {
    return "%s:%s".formatted(
      value.name().toString(),
      Long.toUnsignedString(value.version())
    );
  }

  @Override
  public NPToolExecutionIdentifier exampleValue()
  {
    return NPToolExecutionIdentifier.of("org.apache.maven", 3L);
  }

  @Override
  public String syntax()
  {
    return "<execution-name> ':' <execution-version>";
  }

  @Override
  public Class<NPToolExecutionIdentifier> convertedClass()
  {
    return NPToolExecutionIdentifier.class;
  }
}
