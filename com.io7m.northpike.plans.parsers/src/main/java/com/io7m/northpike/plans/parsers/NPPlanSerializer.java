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


package com.io7m.northpike.plans.parsers;

import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.v1.NPP1Serializer;

import javax.xml.stream.XMLStreamException;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.util.Objects;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A serializer for plans.
 */

public final class NPPlanSerializer
{
  private final OutputStream outputStream;

  private NPPlanSerializer(
    final OutputStream inOutputStream)
  {
    this.outputStream =
      Objects.requireNonNull(inOutputStream, "outputStream");
  }

  /**
   * A serializer for plans.
   *
   * @param outputStream The output stream
   *
   * @return A serializer
   */

  public static NPPlanSerializer create(
    final OutputStream outputStream)
  {
    return new NPPlanSerializer(outputStream);
  }

  /**
   * Execute the serializer.
   *
   * @param plan The plan
   *
   * @throws XMLStreamException On errors
   */

  public void execute(
    final NPPlanType plan)
    throws XMLStreamException
  {
    NPP1Serializer.create(this.outputStream)
      .serialize(plan);
  }

  /**
   * Serialize a plan to a string.
   *
   * @param plan The plan
   *
   * @return The serialized plan
   */

  public static String serializeToString(
    final NPPlanType plan)
  {
    try (var output = new ByteArrayOutputStream()) {
      create(output).execute(plan);
      return output.toString(UTF_8);
    } catch (final IOException | XMLStreamException e) {
      throw new UncheckedIOException(new IOException(e));
    }
  }
}
