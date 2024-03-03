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

import com.io7m.northpike.toolexecj.api.NPTJProgramType;
import org.slf4j.LoggerFactory;
import org.slf4j.Logger;

import javax.tools.FileObject;
import javax.tools.ForwardingJavaFileManager;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.function.Function;

public final class NPTJProgramFileManager
  extends ForwardingJavaFileManager<JavaFileManager>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTJProgramFileManager.class);

  private final List<JavaFileObject> apiBytecode;
  private final List<NPTJProgramSource> compilationUnits;
  private final Function<byte[], byte[]> bytecodeTransformer;
  private final HashMap<String, NPTJProgramBytecode> outputFiles;
  private final NPTJClassLoader classLoader;

  public NPTJProgramFileManager(
    final JavaFileManager delegate,
    final NPTJClassLoader inClassLoader,
    final List<JavaFileObject> inApiBytecode,
    final List<NPTJProgramSource> units,
    final Function<byte[], byte[]> inTransformer)
  {
    super(Objects.requireNonNull(delegate, "delegate"));

    this.apiBytecode =
      Objects.requireNonNull(inApiBytecode, "apiBytecode");
    this.compilationUnits =
      Objects.requireNonNull(units, "compilationUnits");
    this.classLoader =
      Objects.requireNonNull(inClassLoader, "classLoader");
    this.bytecodeTransformer =
      Objects.requireNonNull(inTransformer, "inBytecodeTransformer");
    this.outputFiles =
      new HashMap<>();
  }

  public Map<String, NPTJProgramBytecode> outputFiles()
  {
    return Map.copyOf(this.outputFiles);
  }

  @Override
  public String inferBinaryName(
    final Location location,
    final JavaFileObject file)
  {
    if (file instanceof final NPTJProgramBytecode bytecode) {
      return bytecode.binaryName();
    }
    return super.inferBinaryName(location, file);
  }

  @Override
  public boolean isSameFile(
    final FileObject a,
    final FileObject b)
  {
    return super.isSameFile(a, b);
  }

  @Override
  public boolean handleOption(
    final String current,
    final Iterator<String> remaining)
  {
    return super.handleOption(current, remaining);
  }

  @Override
  public int isSupportedOption(
    final String option)
  {
    return super.isSupportedOption(option);
  }

  @Override
  public JavaFileObject getJavaFileForOutputForOriginatingFiles(
    final Location location,
    final String className,
    final JavaFileObject.Kind kind,
    final FileObject... originatingFiles)
    throws IOException
  {
    LOG.trace("getJavaFileForOutputForOriginatingFiles: {} {} {}", location, className, kind);
    return super.getJavaFileForOutputForOriginatingFiles(
      location,
      className,
      kind,
      originatingFiles
    );
  }

  @Override
  public FileObject getFileForOutput(
    final Location location,
    final String packageName,
    final String relativeName,
    final FileObject sibling)
    throws IOException
  {
    LOG.trace("getFileForOutput: {} {}", location, packageName);
    return super.getFileForOutput(location, packageName, relativeName, sibling);
  }

  @Override
  public FileObject getFileForOutputForOriginatingFiles(
    final Location location,
    final String packageName,
    final String relativeName,
    final FileObject... originatingFiles)
    throws IOException
  {
    LOG.trace("getFileForOutputForOriginatingFiles: {} {}", location, packageName);
    return super.getFileForOutputForOriginatingFiles(
      location,
      packageName,
      relativeName,
      originatingFiles
    );
  }

  @Override
  public Location getLocationForModule(
    final Location location,
    final String moduleName)
    throws IOException
  {
    LOG.trace("getLocationForModule: {} {}", location, moduleName);
    return super.getLocationForModule(location, moduleName);
  }

  @Override
  public Location getLocationForModule(
    final Location location,
    final JavaFileObject fo)
    throws IOException
  {
    LOG.trace("getLocationForModule: {} {}", location, fo);
    return super.getLocationForModule(location, fo);
  }

  @Override
  public <S> ServiceLoader<S> getServiceLoader(
    final Location location,
    final Class<S> service)
    throws IOException
  {
    LOG.trace("getServiceLoader: {} {}", location, service);
    return super.getServiceLoader(location, service);
  }

  @Override
  public String inferModuleName(
    final Location location)
    throws IOException
  {
    LOG.trace("inferModuleName: {}", location);
    return super.inferModuleName(location);
  }

  @Override
  public Iterable<Set<Location>> listLocationsForModules(
    final Location location)
    throws IOException
  {
    LOG.trace("listLocationsForModules: {}", location);
    return super.listLocationsForModules(location);
  }

  @Override
  public boolean contains(
    final Location location,
    final FileObject fo)
    throws IOException
  {
    LOG.trace("contains: {} {}", location, fo);
    return super.contains(location, fo);
  }

  @Override
  public Iterable<JavaFileObject> list(
    final Location location,
    final String packageName,
    final Set<JavaFileObject.Kind> kinds,
    final boolean recurse)
    throws IOException
  {
    LOG.trace("list: {} {} {}", location, packageName, kinds);

    if (Objects.equals(location.getName(), "CLASS_PATH")
        && Objects.equals(packageName, NPTJProgramType.class.getPackageName())) {
      LOG.trace("list: returning API bytecode");
      return List.copyOf(this.apiBytecode);
    }

    return super.list(location, packageName, kinds, recurse);
  }

  @Override
  public boolean hasLocation(
    final Location location)
  {
    LOG.trace("hasLocation: {}", location);
    return super.hasLocation(location);
  }

  @Override
  public ClassLoader getClassLoader(
    final Location location)
  {
    LOG.trace("getClassLoader: {}", location);
    return this.classLoader;
  }

  @Override
  public JavaFileObject getJavaFileForInput(
    final Location location,
    final String className,
    final JavaFileObject.Kind kind)
    throws IOException
  {
    LOG.trace("getJavaFileForInput: {} {} {}", location, className, kind);
    return super.getJavaFileForInput(location, className, kind);
  }

  @Override
  public FileObject getFileForInput(
    final Location location,
    final String packageName,
    final String relativeName)
    throws IOException
  {
    LOG.trace("getFileForInput: {} {}", location, packageName);
    return super.getFileForInput(location, packageName, relativeName);
  }

  @Override
  public JavaFileObject getJavaFileForOutput(
    final Location location,
    final String className,
    final JavaFileObject.Kind kind,
    final FileObject sibling)
  {
    final var file = new NPTJProgramBytecode(className, this.bytecodeTransformer);
    this.outputFiles.put(className, file);
    return file;
  }
}
