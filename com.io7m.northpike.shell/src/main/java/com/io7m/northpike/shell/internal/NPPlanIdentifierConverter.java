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


import com.io7m.northpike.model.NPValidityException;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see NPPlanIdentifier
 */

public final class NPPlanIdentifierConverter
  implements QValueConverterType<NPPlanIdentifier>
{
  /**
   * @see NPPlanIdentifier
   */

  public NPPlanIdentifierConverter()
  {

  }

  @Override
  public NPPlanIdentifier convertFromString(
    final String text)
  {
    final var segments = text.split(":");
    if (segments.length == 2) {
      return NPPlanIdentifier.of(
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
    final NPPlanIdentifier value)
  {
    return "%s:%s".formatted(
      value.name().toString(),
      Long.toUnsignedString(value.version())
    );
  }

  @Override
  public NPPlanIdentifier exampleValue()
  {
    return NPPlanIdentifier.of("org.apache.maven", 3L);
  }

  @Override
  public String syntax()
  {
    return "<plan-name> ':' <plan-version>";
  }

  @Override
  public Class<NPPlanIdentifier> convertedClass()
  {
    return NPPlanIdentifier.class;
  }
}
