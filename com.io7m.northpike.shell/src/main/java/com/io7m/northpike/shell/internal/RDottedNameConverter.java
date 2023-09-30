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

import com.io7m.lanark.core.RDottedName;
import com.io7m.lanark.core.RDottedNamePatterns;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see RDottedName
 */

public final class RDottedNameConverter
  implements QValueConverterType<RDottedName>
{
  static final String UUID_SYNTAX =
    "[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}";

  /**
   * @see RDottedName
   */

  public RDottedNameConverter()
  {

  }

  @Override
  public RDottedName convertFromString(
    final String text)
  {
    return new RDottedName(text);
  }

  @Override
  public String convertToString(
    final RDottedName value)
  {
    return value.toString();
  }

  @Override
  public RDottedName exampleValue()
  {
    return new RDottedName("com.io7m.example");
  }

  @Override
  public String syntax()
  {
    return RDottedNamePatterns.dottedName().pattern();
  }

  @Override
  public Class<RDottedName> convertedClass()
  {
    return RDottedName.class;
  }
}
