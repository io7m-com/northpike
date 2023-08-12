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


package com.io7m.northpike.agent.expressions;

import com.io7m.northpike.agent.expressions.v1.NAE1Serializer;
import com.io7m.northpike.model.NPAgentLabelMatchType;

import javax.xml.stream.XMLStreamException;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.util.Objects;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A serializer for agent label match expressions.
 */

public final class NPASerializer
{
  private final OutputStream outputStream;

  private NPASerializer(
    final OutputStream inOutputStream)
  {
    this.outputStream =
      Objects.requireNonNull(inOutputStream, "outputStream");
  }

  /**
   * A serializer for agent label match expressions.
   *
   * @param outputStream The output stream
   *
   * @return A serializer
   */

  public static NPASerializer create(
    final OutputStream outputStream)
  {
    return new NPASerializer(outputStream);
  }

  /**
   * Execute the serializer.
   *
   * @param expression The expression
   *
   * @throws XMLStreamException On errors
   */

  public void execute(
    final NPAgentLabelMatchType expression)
    throws XMLStreamException
  {
    NAE1Serializer.create(this.outputStream)
      .serialize(expression);
  }

  /**
   * Serialize an agent label match expression to a string.
   *
   * @param expression The expression
   *
   * @return The serialized expression
   */

  public static String serializeToString(
    final NPAgentLabelMatchType expression)
  {
    try (var output = new ByteArrayOutputStream()) {
      create(output).execute(expression);
      return output.toString(UTF_8);
    } catch (final IOException | XMLStreamException e) {
      throw new UncheckedIOException(new IOException(e));
    }
  }
}
