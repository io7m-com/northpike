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

import com.io7m.northpike.model.NPKey;
import com.io7m.quarrel.core.QValueConverterType;

import java.security.NoSuchAlgorithmException;

/**
 * @see NPKey
 */

public final class NPKeyConverter
  implements QValueConverterType<NPKey>
{
  /**
   * @see NPKey
   */

  public NPKeyConverter()
  {

  }

  @Override
  public NPKey convertFromString(
    final String text)
  {
    return NPKey.parse(text);
  }

  @Override
  public String convertToString(
    final NPKey value)
  {
    return value.format();
  }

  @Override
  public NPKey exampleValue()
  {
    try {
      return NPKey.generate();
    } catch (final NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  public String syntax()
  {
    return NPKey.validKeyPattern().pattern();
  }

  @Override
  public Class<NPKey> convertedClass()
  {
    return NPKey.class;
  }
}
