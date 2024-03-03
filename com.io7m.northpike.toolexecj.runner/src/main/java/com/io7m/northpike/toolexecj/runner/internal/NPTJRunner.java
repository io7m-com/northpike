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

import com.io7m.northpike.toolexecj.runner.NPTJEvaluation;
import com.io7m.northpike.toolexecj.runner.NPTJException;
import com.io7m.northpike.toolexecj.runner.NPTJRunnerType;
import org.graalvm.polyglot.Context;
import org.graalvm.polyglot.ResourceLimits;
import org.graalvm.polyglot.SandboxPolicy;
import org.graalvm.polyglot.Source;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorToolExecutionFailed;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A GraalVM based runner.
 */

public final class NPTJRunner
  implements NPTJRunnerType
{
  private final BigInteger executionId;
  private final Map<String, String> initialEnvironment;
  private final String program;

  /**
   * A GraalVM based runner.
   *
   * @param inExecutionId        The execution ID
   * @param inInitialEnvironment The initial environment
   * @param inProgram            The program text
   */

  public NPTJRunner(
    final BigInteger inExecutionId,
    final Map<String, String> inInitialEnvironment,
    final String inProgram)
  {
    this.executionId =
      Objects.requireNonNull(inExecutionId, "executionId");
    this.initialEnvironment =
      Objects.requireNonNull(inInitialEnvironment, "initialEnvironment");
    this.program =
      Objects.requireNonNull(inProgram, "program");
  }

  @Override
  public NPTJEvaluation execute()
    throws NPTJException
  {
    final var programName =
      "urn:toolexecution:%s".formatted(this.executionId);

    final Source source;
    try {
      source = Source.newBuilder("js", this.program, programName)
        .build();
    } catch (final IOException e) {
      throw new NPTJException(
        e.getMessage(),
        e,
        errorIo(),
        Map.of(),
        Optional.empty(),
        List.of()
      );
    }

    final var outputStream =
      new ByteArrayOutputStream();
    final var errStream =
      new ByteArrayOutputStream();
    final var execContext =
      new NPTJExecContext(this.initialEnvironment);

    try {
      final var contextBuilder =
        Context.newBuilder("js")
          .sandbox(SandboxPolicy.CONSTRAINED)
          .resourceLimits(
            ResourceLimits.newBuilder()
              .statementLimit(1000L, s -> true)
              .build())
          .err(errStream)
          .out(outputStream);

      try (var context = contextBuilder.build()) {
        final var bindings = context.getBindings("js");
        bindings.putMember("execution", execContext);
        context.eval(source);
      }

      return new NPTJEvaluation(
        Map.copyOf(execContext.environment()),
        List.copyOf(execContext.arguments()),
        linesOf(outputStream, errStream)
      );
    } catch (final Exception e) {
      throw new NPTJException(
        e.getMessage(),
        e,
        errorToolExecutionFailed(),
        lineAttributesOf(outputStream, errStream),
        Optional.empty(),
        List.of()
      );
    }
  }

  private static Map<String, String> lineAttributesOf(
    final ByteArrayOutputStream outputStream,
    final ByteArrayOutputStream errStream)
  {
    final var attributes = new HashMap<String, String>();
    final var lines = linesOf(outputStream, errStream);
    for (int index = 0; index < lines.size(); ++index) {
      attributes.put(
        "Output[%d]".formatted(Integer.valueOf(index)),
        lines.get(index)
      );
    }
    return Map.copyOf(attributes);
  }

  private static List<String> linesOf(
    final ByteArrayOutputStream outputStream,
    final ByteArrayOutputStream errStream)
  {
    final var lines = new ArrayList<String>();
    lines.addAll(outputStream.toString(UTF_8).lines().toList());
    lines.addAll(errStream.toString(UTF_8).lines().toList());
    return List.copyOf(lines);
  }
}
