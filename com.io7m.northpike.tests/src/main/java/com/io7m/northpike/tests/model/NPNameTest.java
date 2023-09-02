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

import com.io7m.northpike.model.NPAgentResourceName;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReferenceName;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPNameTest
{
  @Property
  public void testAgentResourceName(
    final @ForAll NPAgentResourceName name)
  {
    assertEquals(name, name);
    assertEquals(0, name.compareTo(name));
  }

  @Property
  public void testFormatName(
    final @ForAll NPFormatName name)
  {
    assertEquals(name, name);
    assertEquals(0, name.compareTo(name));
  }

  @Property
  public void testToolName(
    final @ForAll NPToolName name)
  {
    assertEquals(name, name);
    assertEquals(0, name.compareTo(name));
  }

  @Property
  public void testToolReferenceName(
    final @ForAll NPToolReferenceName name)
  {
    assertEquals(name, name);
    assertEquals(0, name.compareTo(name));
  }

  @Property
  public void testToolExecutionName(
    final @ForAll NPToolExecutionName name)
  {
    assertEquals(name, name);
    assertEquals(0, name.compareTo(name));
  }
}
