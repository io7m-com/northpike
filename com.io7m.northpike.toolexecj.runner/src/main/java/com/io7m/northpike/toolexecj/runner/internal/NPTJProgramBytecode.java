/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.toolexecj.runner.internal;

import javax.tools.SimpleJavaFileObject;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;
import java.util.Objects;
import java.util.function.Function;

public final class NPTJProgramBytecode
  extends SimpleJavaFileObject
{
  private final String binaryName;
  private final Function<byte[], byte[]> bytecodeTransformer;
  private final ByteArrayOutputStream bytecodeStream;

  public NPTJProgramBytecode(
    final String className,
    final Function<byte[], byte[]> inTransformer)
  {
    super(
      URI.create("urn:/%s.class".formatted(className)),
      Kind.CLASS
    );
    this.binaryName =
      className;
    this.bytecodeTransformer =
      Objects.requireNonNull(inTransformer, "bytecodeTransformer");
    this.bytecodeStream =
      new ByteArrayOutputStream();
  }

  @Override
  public InputStream openInputStream()
  {
    return new ByteArrayInputStream(
      this.bytecodeTransformer.apply(this.bytecodeStream.toByteArray())
    );
  }

  @Override
  public OutputStream openOutputStream()
  {
    return this.bytecodeStream;
  }

  public String binaryName()
  {
    return this.binaryName;
  }
}
