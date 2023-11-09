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

import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.UUID;

/**
 * @see NPRepositoryID
 */

public final class NPRepositoryIDConverter
  implements QValueConverterType<NPRepositoryID>
{
  static final String UUID_SYNTAX =
    "[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}";

  /**
   * @see NPRepositoryID
   */

  public NPRepositoryIDConverter()
  {

  }

  @Override
  public NPRepositoryID convertFromString(
    final String text)
  {
    return new NPRepositoryID(UUID.fromString(text));
  }

  @Override
  public String convertToString(
    final NPRepositoryID value)
  {
    return value.toString();
  }

  @Override
  public NPRepositoryID exampleValue()
  {
    return new NPRepositoryID(UUID.randomUUID());
  }

  @Override
  public String syntax()
  {
    return UUID_SYNTAX;
  }

  @Override
  public Class<NPRepositoryID> convertedClass()
  {
    return NPRepositoryID.class;
  }
}
