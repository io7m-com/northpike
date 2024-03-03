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

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.security.SecureClassLoader;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

public final class NPTJClassLoader extends SecureClassLoader
{
  private final Set<String> permittedClasses;
  private final Map<String, byte[]> classBytes;

  @Override
  public String toString()
  {
    return "[TEClassLoader %s]".formatted(this.getName());
  }

  public NPTJClassLoader(
    final String inName,
    final ClassLoader inParent,
    final Set<String> inPermittedClasses)
  {
    super(
      Objects.requireNonNull(inName, "name"),
      Objects.requireNonNull(inParent, "parent")
    );
    this.permittedClasses =
      Set.copyOf(inPermittedClasses);
    this.classBytes =
      new HashMap<>();
  }

  public void setClassBytes(
    final String name,
    final byte[] bytecode)
  {
    this.classBytes.put(
      Objects.requireNonNull(name, "name"),
      Objects.requireNonNull(bytecode, "bytecode")
    );
  }

  @Override
  public Class<?> loadClass(
    final String name)
    throws ClassNotFoundException
  {
    Objects.requireNonNull(name, "name");

    final var data = this.classBytes.get(name);
    if (data != null) {
      return this.defineClass(name, data, 0, data.length);
    }

    if (!this.permittedClasses.contains(name)) {
      throw new SecurityException(
        "Loading class %s is not permitted.".formatted(name)
      );
    }

    return super.loadClass(name);
  }

  @Override
  public URL getResource(
    final String name)
  {
    Objects.requireNonNull(name, "name");
    return super.getResource(name);
  }

  @Override
  public Enumeration<URL> getResources(
    final String name)
    throws IOException
  {
    Objects.requireNonNull(name, "name");
    return super.getResources(name);
  }

  @Override
  public Stream<URL> resources(
    final String name)
  {
    Objects.requireNonNull(name, "name");
    return super.resources(name);
  }

  @Override
  public InputStream getResourceAsStream(
    final String name)
  {
    Objects.requireNonNull(name, "name");
    return super.getResourceAsStream(name);
  }

  @Override
  public void setDefaultAssertionStatus(
    final boolean enabled)
  {
    super.setDefaultAssertionStatus(enabled);
  }

  @Override
  public void setPackageAssertionStatus(
    final String packageName,
    final boolean enabled)
  {
    super.setPackageAssertionStatus(packageName, enabled);
  }

  @Override
  public void setClassAssertionStatus(
    final String className,
    final boolean enabled)
  {
    super.setClassAssertionStatus(className, enabled);
  }

  @Override
  public void clearAssertionStatus()
  {
    super.clearAssertionStatus();
  }
}
