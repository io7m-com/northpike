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


package com.io7m.northpike.tests.toolexec;

import com.io7m.northpike.model.NPPreserveLexical;
import com.io7m.northpike.toolexec.model.NPTXDescription;
import com.io7m.northpike.toolexec.parser.NPTXDescriptionParser;
import com.io7m.northpike.toolexec.serializer.v1.NPTX1Serializer;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.net.URI;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPTXParsingTest
{
  @Property
  public void testRoundTrip(
    final @ForAll NPTXDescription description)
    throws Exception
  {
    final var output =
      new ByteArrayOutputStream();
    final var serializer =
      NPTX1Serializer.create(output);

    serializer.execute(description);

    final var input =
      new ByteArrayInputStream(output.toByteArray());

    final var parser =
      NPTXDescriptionParser.open(
        input,
        URI.create("urn:stdin"),
        NPPreserveLexical.DISCARD_LEXICAL_INFORMATION,
        parseStatus -> {

        });

    final NPTXDescription result = parser.execute();
    assertEquals(description, result);
  }
}
