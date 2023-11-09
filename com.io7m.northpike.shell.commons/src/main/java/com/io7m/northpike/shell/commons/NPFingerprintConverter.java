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

import com.io7m.northpike.model.NPFingerprint;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see NPFingerprint
 */

public final class NPFingerprintConverter
  implements QValueConverterType<NPFingerprint>
{
  /**
   * @see NPFingerprint
   */

  public NPFingerprintConverter()
  {

  }

  @Override
  public NPFingerprint convertFromString(
    final String text)
  {
    return new NPFingerprint(text);
  }

  @Override
  public String convertToString(
    final NPFingerprint value)
  {
    return value.toString();
  }

  @Override
  public NPFingerprint exampleValue()
  {
    return new NPFingerprint("79c9d3b52db46780c17771af9b6adba81ee082b1");
  }

  @Override
  public String syntax()
  {
    return NPFingerprint.syntax();
  }

  @Override
  public Class<NPFingerprint> convertedClass()
  {
    return NPFingerprint.class;
  }
}
