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

package com.io7m.northpike.tools.common;

import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolException;
import com.io7m.northpike.tools.api.NPToolProgramResult;
import org.slf4j.Logger;
import org.slf4j.MDC;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;

/**
 * Functions to execute external processes.
 */

public final class NPToolExecutions
{
  private NPToolExecutions()
  {

  }

  /**
   * Execute a program. The program's output will be logged in real-time to
   * {@code logger}. The program will be executed in the given directory.
   * The method will only return when the process exits (or if interrupted).
   *
   * @param logger             The logger
   * @param strings            The string resources
   * @param executionDirectory The starting directory for the new process
   * @param execution          The command and arguments
   *
   * @return The result of execution
   *
   * @throws InterruptedException On interruption
   * @throws NPToolException      On errors
   */

  public static NPToolProgramResult execute(
    final Logger logger,
    final NPStrings strings,
    final Path executionDirectory,
    final List<String> execution)
    throws InterruptedException, NPToolException
  {
    try (var resources =
           NPToolResources.createResourceCollection(strings)) {

      final var executor =
        resources.add(
          Executors.newThreadPerTaskExecutor(
            Thread.ofVirtual()
              .name("com.io7m.northpike.toolexec-", 0L)
              .factory()
          )
        );

      try {
        final var builder =
          new ProcessBuilder()
            .command(execution);

        builder.directory(executionDirectory.toFile());
        builder.redirectError(ProcessBuilder.Redirect.PIPE);
        builder.redirectErrorStream(true);
        builder.redirectOutput(ProcessBuilder.Redirect.PIPE);

        final var output = new LinkedBlockingQueue<String>();
        final var process = builder.start();
        executor.execute(() -> {
          MDC.put("ProcessID", String.valueOf(process.pid()));
          MDC.put("Program", execution.get(0));

          try (var reader = process.inputReader()) {
            while (true) {
              final var line = reader.readLine();
              if (line == null) {
                break;
              }
              logger.debug("{}", line);
              output.add(line);
            }
          } catch (final IOException e) {
            output.add("%s: %s".formatted(e.getClass(), e.getMessage()));
          }
        });

        final var exitCode = process.waitFor();
        process.destroyForcibly();
        return new NPToolProgramResult(execution, exitCode, output);
      } catch (final IOException e) {
        throw NPToolExceptions.errorIO(strings, e);
      }
    }
  }
}
