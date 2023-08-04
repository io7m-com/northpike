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


package com.io7m.northpike.tests.parsers;

import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.parsers.NPAgentLabelMatchExpressions;
import com.io7m.northpike.strings.NPStrings;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.util.stream.Stream;

import static java.util.Locale.ROOT;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class NPAgentLabelMatchExpressionsTest
{
  @Property
  public void testRoundTrip(
    final @ForAll NPAgentLabelMatchType v)
    throws NPException
  {
    final var e = new NPAgentLabelMatchExpressions(NPStrings.create(ROOT));
    final var s = e.matchSerializeToString(v);
    final var r = e.match(s);
    assertEquals(r, v);
  }

  @TestFactory
  public Stream<DynamicTest> testParseErrors()
  {
    return Stream.of(
        "[",
        ")",
        "[)",
      "x",
      "with-label",
      "[with-label X]",
      "[with-label []]",
      "[with-label x y]",
      "[any-label x]",
      "[and [with-label x] [with-label y] [with-label z]]",
      "[and [with-label x]]",
      "[or [with-label x] [with-label y] [with-label z]]",
      "[or [with-label x]]"
      )
      .map(text -> {
        return DynamicTest.dynamicTest(text, () -> {
          final var e = new NPAgentLabelMatchExpressions(NPStrings.create(ROOT));
          assertThrows(NPException.class, () -> e.match(text));
        });
      });
  }
}
