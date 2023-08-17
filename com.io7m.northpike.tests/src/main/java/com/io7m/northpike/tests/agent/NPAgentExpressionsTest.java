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


package com.io7m.northpike.tests.agent;

import com.io7m.anethum.api.ParsingException;
import com.io7m.anethum.slf4j.ParseStatusLogging;
import com.io7m.northpike.agent.expressions.NPAEParser;
import com.io7m.northpike.agent.expressions.NPASerializer;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPPreserveLexical;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.ByteArrayInputStream;
import java.net.URI;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;

public final class NPAgentExpressionsTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentExpressionsTest.class);

  @Property
  public void testParser(
    final @ForAll NPAgentLabelMatchType match)
    throws ParsingException
  {
    final var serialized =
      NPASerializer.serializeToString(match);

    final var parsed =
      NPAEParser.open(
        new ByteArrayInputStream(serialized.getBytes(StandardCharsets.UTF_8)),
        URI.create("urn:input"),
        NPPreserveLexical.DISCARD_LEXICAL_INFORMATION,
        status -> ParseStatusLogging.logWithAll(LOG, status)
      ).execute();

    assertEquals(match, parsed);
  }
}
