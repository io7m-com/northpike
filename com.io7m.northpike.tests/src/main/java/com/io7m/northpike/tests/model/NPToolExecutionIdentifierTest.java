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


package com.io7m.northpike.tests.model;

import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class NPToolExecutionIdentifierTest
{
  @Property
  public void testValue(
    final @ForAll NPToolExecutionIdentifier x)
  {
    assertEquals(x, x);
    assertEquals(0, x.compareTo(x));
  }

  @Property
  public void testVersion(
    final @ForAll NPToolExecutionName x)
  {
    assertTrue(
      new NPToolExecutionIdentifier(x, 0L)
        .compareTo(new NPToolExecutionIdentifier(x, 1L)) < 0
    );
  }
}
