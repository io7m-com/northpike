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


package com.io7m.northpike.toolexecj.runner;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexecj.runner.internal.NPTJProgramBytecode;
import com.io7m.northpike.toolexecj.runner.internal.NPTJRunner;
import org.objectweb.asm.ClassReader;

import javax.tools.JavaFileObject;
import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.NoSuchFileException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.zip.ZipFile;
import java.util.zip.ZipInputStream;

public final class NPTJRunners implements NPTJRunnerServiceType
{
  private static final Object EXECUTION_ID_LOCK = new Object();
  private static BigInteger EXECUTION_ID = BigInteger.ZERO;
  private final Set<String> permittedClasses;
  private final List<JavaFileObject> apiBytecode;
  private final NPStrings strings;

  private NPTJRunners(
    final NPStrings inStrings,
    final Set<String> inPermittedClasses,
    final List<JavaFileObject> inApiBytecode)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.permittedClasses =
      Objects.requireNonNull(inPermittedClasses, "permittedClasses");
    this.apiBytecode =
      Objects.requireNonNull(inApiBytecode, "apiBytecode");
  }

  public static NPTJRunnerServiceType create(
    final NPStrings strings)
    throws IOException
  {
    final var permittedClasses =
      openPermittedClassesList();
    final var apiBytecode =
      retrieveAPIClassesBytecode();

    return new NPTJRunners(strings, permittedClasses, apiBytecode);
  }

  private static BigInteger freshId()
  {
    synchronized (EXECUTION_ID_LOCK) {
      final var now = EXECUTION_ID;
      EXECUTION_ID = EXECUTION_ID.add(BigInteger.ONE);
      return now;
    }
  }

  private static Set<String> openPermittedClassesList()
  {
    final var names = new HashSet<String>();
    try (var stream = NPTJRunner.class.getResourceAsStream(
      "/com/io7m/northpike/toolexecj/runner/internal/PermittedClasses.txt")) {
      try (var reader =
             new BufferedReader(new InputStreamReader(
               stream,
               StandardCharsets.UTF_8))) {
        while (true) {
          final var line = reader.readLine();
          if (line == null) {
            break;
          }
          final var trimmed = line.trim();
          if (trimmed.isEmpty()) {
            continue;
          }
          if (trimmed.startsWith("#")) {
            continue;
          }
          names.add(trimmed);
        }
      }
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
    return Set.copyOf(names);
  }

  private static List<JavaFileObject> retrieveAPIClassesBytecode()
    throws IOException
  {
    final var classFiles =
      new ArrayList<JavaFileObject>();

    final var archiveBase =
      "/com/io7m/northpike/toolexecj/runner/internal/com.io7m.northpike.toolexecj.api.jar";

    try (var resources = CloseableCollection.create(IOException::new)) {
      final var baseStream =
        resources.add(NPTJRunners.class.getResourceAsStream(archiveBase));
      final var buffered =
        resources.add(new BufferedInputStream(baseStream));
      final var zipStream =
        resources.add(new ZipInputStream(buffered));

      while (true) {
        final var entry = zipStream.getNextEntry();
        if (entry == null) {
          break;
        }
        if (entry.isDirectory()) {
          continue;
        }
        final var entryName = entry.getName();
        if (!entryName.endsWith(".class")) {
          continue;
        }
        if (entryName.endsWith("package-info.class")) {
          continue;
        }

        final var bytecode =
          zipStream.readAllBytes();
        final var reader =
          new ClassReader(bytecode);
        final var className =
          reader.getClassName();
        final var classFile =
          new NPTJProgramBytecode(className, Function.identity());

        try (var outputStream = classFile.openOutputStream()) {
          outputStream.write(bytecode);
        }

        classFiles.add(classFile);
      }
    }

    return List.copyOf(classFiles);
  }

  @Override
  public NPTJRunnerType create(
    final String className,
    final String program,
    final Function<byte[], byte[]> bytecodeTransformer)
  {
    return new NPTJRunner(
      this.strings,
      this.permittedClasses,
      this.apiBytecode,
      freshId(),
      className,
      program,
      bytecodeTransformer
    );
  }

  @Override
  public String description()
  {
    return "Toolexec/Java runner service.";
  }
}
