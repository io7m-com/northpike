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
import com.io7m.northpike.model.NPToolExecutionIdentifierSet;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @see NPToolExecutionIdentifierSet
 */

public final class NPToolExecutionIdentifierSetConverter
  implements QValueConverterType<NPToolExecutionIdentifierSet>
{
  private static final NPToolExecutionIdentifierConverter IDENTIFIER_CONVERTER =
    new NPToolExecutionIdentifierConverter();

  /**
   * @see NPToolExecutionIdentifierSet
   */

  public NPToolExecutionIdentifierSetConverter()
  {

  }

  @Override
  public NPToolExecutionIdentifierSet convertFromString(
    final String text)
  {
    if (text.trim().isEmpty()) {
      return new NPToolExecutionIdentifierSet(Set.of());
    }

    return new NPToolExecutionIdentifierSet(
      Arrays.stream(text.split(","))
        .map(IDENTIFIER_CONVERTER::convertFromString)
        .collect(Collectors.toUnmodifiableSet())
    );
  }

  @Override
  public String convertToString(
    final NPToolExecutionIdentifierSet value)
  {
    return value.identifiers()
      .stream()
      .map(IDENTIFIER_CONVERTER::convertToString)
      .collect(Collectors.joining(","));
  }

  @Override
  public NPToolExecutionIdentifierSet exampleValue()
  {
    return new NPToolExecutionIdentifierSet(
      Set.of(
        NPToolExecutionIdentifier.of("com.io7m.example", 23L),
        NPToolExecutionIdentifier.of("org.apache.maven", 3L),
        NPToolExecutionIdentifier.of("com.example", 100L)
      )
    );
  }

  @Override
  public String syntax()
  {
    return "%s [ ',' %s ] ".formatted(
      IDENTIFIER_CONVERTER.syntax(),
      IDENTIFIER_CONVERTER.syntax()
    );
  }

  @Override
  public Class<NPToolExecutionIdentifierSet> convertedClass()
  {
    return NPToolExecutionIdentifierSet.class;
  }
}
