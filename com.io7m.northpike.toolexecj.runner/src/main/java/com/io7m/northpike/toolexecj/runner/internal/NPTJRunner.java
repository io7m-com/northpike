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

import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexecj.api.NPTJContextType;
import com.io7m.northpike.toolexecj.runner.NPTJEvaluation;
import com.io7m.northpike.toolexecj.runner.NPTJException;
import com.io7m.northpike.toolexecj.runner.NPTJRunnerType;
import com.io7m.seltzer.api.SStructuredError;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaFileObject;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorCompilationFailed;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorSecurityPolicyDenied;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorToolExecutionFailed;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_CLASS_CONSTRUCTOR;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_CLASS_CONSTRUCTOR_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_CLASS_LOAD_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_COMPILATION_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_EXECUTE_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_EXECUTE_METHOD_LOOKUP;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_EXECUTE_SECURITY;
import static com.io7m.northpike.strings.NPStringConstants.TOOLEXECJ_NO_SYSTEM_COMPILER;

public final class NPTJRunner
  implements NPTJRunnerType
{
  private final NPStrings strings;
  private final Set<String> permittedClassNames;
  private final List<JavaFileObject> apiBytecode;
  private final BigInteger executionId;
  private final String className;
  private final String programText;
  private final Function<byte[], byte[]> bytecodeTransformer;
  private final ArrayList<SStructuredError<String>> errors;
  private final NPTJClassLoader classLoader;

  public NPTJRunner(
    final NPStrings inStrings,
    final Set<String> inNames,
    final List<JavaFileObject> inApiBytecode,
    final BigInteger inExecutionId,
    final String inClassName,
    final String inProgramText,
    final Function<byte[], byte[]> inTransformer)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.permittedClassNames =
      Set.copyOf(inNames);
    this.apiBytecode =
      Objects.requireNonNull(inApiBytecode, "apiBytecode");
    this.executionId =
      Objects.requireNonNull(inExecutionId, "inExecutionId");
    this.className =
      Objects.requireNonNull(inClassName, "className");
    this.programText =
      Objects.requireNonNull(inProgramText, "program");
    this.bytecodeTransformer =
      Objects.requireNonNull(inTransformer, "bytecodeTransformer");
    this.errors =
      new ArrayList<>();
    this.classLoader =
      new NPTJClassLoader(
        "com.io7m.northpike.toolexecj.runner-%s".formatted(this.executionId),
        ClassLoader.getSystemClassLoader(),
        this.permittedClassNames
      );
  }

  @Override
  public NPTJEvaluation execute()
    throws NPTJException
  {
    return this.run(this.compile());
  }

  private NPTJEvaluation run(
    final byte[] classBytes)
    throws NPTJException
  {
    this.classLoader.setClassBytes(this.className, classBytes);

    final var outputMessages =
      new ArrayList<String>();
    final var context =
      new NPTJContextType()
      {
        @Override
        public void log(
          final String format,
          final Object... args)
        {
          outputMessages.add(String.format(format, args));
        }
      };

    final Class<?> classRef;
    try {
      classRef = this.classLoader.loadClass(this.className);
    } catch (final Throwable e) {
      throw this.error(
        TOOLEXECJ_CLASS_LOAD_FAILED,
        new Exception(e),
        errorToolExecutionFailed()
      );
    }

    final Constructor<?> constructor;
    try {
      constructor = classRef.getConstructor(NPTJContextType.class);
    } catch (final Exception e) {
      throw this.error(
        TOOLEXECJ_CLASS_CONSTRUCTOR,
        e,
        errorToolExecutionFailed()
      );
    }

    final Object instance;
    try {
      instance = constructor.newInstance(context);
    } catch (final Exception e) {
      throw this.error(
        TOOLEXECJ_CLASS_CONSTRUCTOR_FAILED,
        e,
        errorToolExecutionFailed()
      );
    }

    final Method method;
    try {
      method = classRef.getMethod("execute");
    } catch (final Exception e) {
      throw this.error(
        TOOLEXECJ_EXECUTE_METHOD_LOOKUP,
        e,
        errorToolExecutionFailed()
      );
    }

    try {
      method.invoke(instance);
    } catch (final InvocationTargetException e) {
      if (e.getCause() instanceof final SecurityException x) {
        throw this.error(
          TOOLEXECJ_EXECUTE_SECURITY,
          x,
          errorSecurityPolicyDenied()
        );
      }
      throw this.error(
        TOOLEXECJ_EXECUTE_FAILED,
        e,
        errorToolExecutionFailed()
      );
    } catch (final Exception e) {
      throw this.error(
        TOOLEXECJ_EXECUTE_FAILED,
        e,
        errorToolExecutionFailed()
      );
    }

    return new NPTJEvaluation(
      Map.of(),
      List.of(),
      List.copyOf(outputMessages)
    );
  }

  private NPTJException error(
    final NPStringConstantType message,
    final Exception cause,
    final NPErrorCode errorCode)
  {
    return new NPTJException(
      this.strings.format(message),
      cause,
      errorCode,
      Map.of(),
      Optional.empty(),
      List.copyOf(this.errors)
    );
  }

  private NPTJException error(
    final NPStringConstantType message,
    final NPErrorCode errorCode)
  {
    return new NPTJException(
      this.strings.format(message),
      errorCode,
      Map.of(),
      Optional.empty(),
      List.copyOf(this.errors)
    );
  }

  private byte[] compile()
    throws NPTJException
  {
    this.errors.clear();

    final var compiler =
      ToolProvider.getSystemJavaCompiler();

    if (compiler == null) {
      throw this.error(
        TOOLEXECJ_NO_SYSTEM_COMPILER,
        errorCompilationFailed()
      );
    }

    final var diagnostics =
      new DiagnosticCollector<JavaFileObject>();

    final var baseFileManager =
      compiler.getStandardFileManager(
        diagnostics,
        Locale.getDefault(),
        StandardCharsets.UTF_8
      );

    final var sourceFile =
      new NPTJProgramSource(this.className, this.programText);
    final var compilationUnits =
      List.of(sourceFile);
    final var fileManager =
      new NPTJProgramFileManager(
        baseFileManager,
        this.classLoader,
        this.apiBytecode,
        compilationUnits,
        this.bytecodeTransformer
      );

    final var task =
      compiler.getTask(
        null,
        fileManager,
        diagnostics,
        List.of("-verbose"),
        null,
        compilationUnits
      );

    final boolean success =
      task.call().booleanValue();

    for (final var diagnostic : diagnostics.getDiagnostics()) {
      final var attributes = new HashMap<String, String>();
      attributes.put("Line", Long.toString(diagnostic.getLineNumber()));
      attributes.put("Column", Long.toString(diagnostic.getColumnNumber()));

      this.errors.add(
        new SStructuredError<>(
          "error-compilation",
          diagnostic.getMessage(Locale.ROOT),
          Map.copyOf(attributes),
          Optional.empty(),
          Optional.empty()
        )
      );
    }

    if (success) {
      final var outputFiles =
        fileManager.outputFiles();
      final var outputFile =
        outputFiles.get(this.className);

      if (outputFile != null) {
        try {
          return outputFile.openInputStream().readAllBytes();
        } catch (final IOException e) {
          throw new NPTJException(
            e.getMessage(),
            e,
            errorIo(),
            Map.of(),
            Optional.empty(),
            List.copyOf(this.errors)
          );
        }
      }
    }

    throw this.error(
      TOOLEXECJ_COMPILATION_FAILED,
      errorCompilationFailed()
    );
  }

}
