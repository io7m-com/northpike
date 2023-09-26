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


package com.io7m.northpike.tests.server.assignments;

import com.io7m.anethum.api.SerializationException;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPPreserveLexical;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerType;

import java.io.IOException;
import java.io.OutputStream;
import java.net.URI;
import java.util.Objects;
import java.util.Set;

import static java.nio.charset.StandardCharsets.UTF_8;

public final class NPGarbageSerializers
  implements NPPlanSerializerFactoryType
{
  public NPGarbageSerializers()
  {

  }

  @Override
  public Set<NPFormatName> formats()
  {
    return new NPPlanParsers().formats();
  }

  @Override
  public NPPlanSerializerType createSerializerWithContext(
    final NPPreserveLexical context,
    final URI target,
    final OutputStream stream)
  {
    return new Serializer(stream);
  }

  @Override
  public String description()
  {
    return "A serializer that always produces nonsense.";
  }

  private static  final class Serializer implements NPPlanSerializerType
  {
    private final OutputStream stream;

    Serializer(
      final OutputStream inStream)
    {
      this.stream = Objects.requireNonNull(inStream, "stream");
    }

    @Override
    public NPFormatName format()
    {
      return new NPPlanParsers()
        .formats()
        .stream()
        .findFirst()
        .orElseThrow();
    }

    @Override
    public void execute(
      final NPPlanType value)
      throws SerializationException
    {
      try {
        this.stream.write("This isn't a plan.".getBytes(UTF_8));
      } catch (final IOException e) {
        throw new SerializationException(e.getMessage(), e);
      }
    }

    @Override
    public void close()
      throws IOException
    {
      this.stream.close();
    }
  }
}
