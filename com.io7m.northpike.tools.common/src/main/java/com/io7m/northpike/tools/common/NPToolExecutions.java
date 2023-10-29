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

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Objects;

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
   * @param environment        The environment
   * @param executionDirectory The starting directory for the new process
   * @param execution          The command and arguments
   * @param receiver           The process output receiver
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
    final Map<String, String> environment,
    final List<String> execution,
    final NPToolProcessOutputReceiverType receiver)
    throws InterruptedException, NPToolException
  {
    Objects.requireNonNull(logger, "logger");
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(executionDirectory, "executionDirectory");
    Objects.requireNonNull(environment, "environment");
    Objects.requireNonNull(execution, "execution");
    Objects.requireNonNull(receiver, "receiver");

    try {
      final var builder = new ProcessBuilder();
      builder.environment().clear();
      builder.environment().putAll(environment);
      builder.command(execution);
      builder.directory(executionDirectory.toFile());
      builder.redirectError(ProcessBuilder.Redirect.PIPE);
      builder.redirectErrorStream(true);
      builder.redirectOutput(ProcessBuilder.Redirect.PIPE);

      final var processName =
        execution.get(0);
      final var process =
        builder.start();
      final var processId =
        Long.toUnsignedString(process.pid());

      final var outThread =
        Thread.ofVirtual()
          .start(() -> {
            processStandardOutput(
              logger,
              receiver,
              processName,
              processId,
              process.inputReader()
            );
          });

      final var errThread =
        Thread.ofVirtual()
          .start(() -> {
            processStandardError(
              logger,
              receiver,
              processName,
              processId,
              process.errorReader()
            );
          });

      final var exitCode = process.waitFor();
      outThread.join();
      errThread.join();

      process.destroyForcibly();
      return new NPToolProgramResult(execution, exitCode);
    } catch (final IOException e) {
      throw NPToolExceptions.errorIO(strings, e);
    }
  }

  private static void processStandardError(
    final Logger logger,
    final NPToolProcessOutputReceiverType receiver,
    final String processName,
    final String processId,
    final BufferedReader reader)
  {
    try (reader) {
      while (true) {
        final var line = reader.readLine();
        if (line == null) {
          break;
        }
        logger.debug("STDERR {}", line);
        try {
          receiver.onReceive(processName, processId, line);
        } catch (final Throwable e) {
          // Ignored
        }
      }
    } catch (final IOException e) {
      try {
        final var text =
          "%s: %s".formatted(e.getClass(), e.getMessage());
        receiver.onReceive(processName, processId, text);
      } catch (final Throwable ex) {
        // Ignored
      }
    }
  }

  private static void processStandardOutput(
    final Logger logger,
    final NPToolProcessOutputReceiverType receiver,
    final String processName,
    final String processId,
    final BufferedReader reader)
  {
    try (reader) {
      while (true) {
        final var line = reader.readLine();
        if (line == null) {
          break;
        }
        logger.debug("STDOUT {}", line);
        try {
          receiver.onReceive(processName, processId, line);
        } catch (final Throwable e) {
          // Ignored
        }
      }
    } catch (final IOException e) {
      try {
        final var text =
          "%s: %s".formatted(e.getClass(), e.getMessage());
        receiver.onReceive(processName, processId, text);
      } catch (final Throwable ex) {
        // Ignored
      }
    }
  }
}
