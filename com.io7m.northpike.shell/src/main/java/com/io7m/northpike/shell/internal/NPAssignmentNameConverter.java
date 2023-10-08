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


import com.io7m.lanark.core.RDottedNamePatterns;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.quarrel.core.QValueConverterType;

/**
 * @see NPAssignmentName
 */

public final class NPAssignmentNameConverter
  implements QValueConverterType<NPAssignmentName>
{
  /**
   * @see NPAssignmentName
   */

  public NPAssignmentNameConverter()
  {

  }

  @Override
  public NPAssignmentName convertFromString(
    final String text)
  {
    return NPAssignmentName.of(text);
  }

  @Override
  public String convertToString(
    final NPAssignmentName value)
  {
    return value.toString();
  }

  @Override
  public NPAssignmentName exampleValue()
  {
    return NPAssignmentName.of("com.io7m.example");
  }

  @Override
  public String syntax()
  {
    return RDottedNamePatterns.dottedName().pattern();
  }

  @Override
  public Class<NPAssignmentName> convertedClass()
  {
    return NPAssignmentName.class;
  }
}
