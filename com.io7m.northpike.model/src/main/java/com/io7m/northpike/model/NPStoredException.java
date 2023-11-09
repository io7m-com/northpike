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


package com.io7m.northpike.model;

import com.io7m.seltzer.api.SStructuredErrorType;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * A description of an exception.
 *
 * @param className  The original exception class name
 * @param message    The exception message
 * @param attributes The attributes
 * @param cause      The cause, if any
 * @param suppressed The suppressed exceptions
 * @param stackTrace The stack trace
 */

public record NPStoredException(
  String className,
  String message,
  Map<String, String> attributes,
  Optional<NPStoredException> cause,
  List<NPStoredException> suppressed,
  List<NPStoredStackTraceElement> stackTrace)
{
  /**
   * A description of an exception.
   *
   * @param className  The original exception class name
   * @param message    The exception message
   * @param attributes The attributes
   * @param cause      The cause, if any
   * @param suppressed The suppressed exceptions
   * @param stackTrace The stack trace
   */

  public NPStoredException
  {
    Objects.requireNonNull(className, "className");
    Objects.requireNonNull(message, "message");
    Objects.requireNonNull(attributes, "attributes");
    Objects.requireNonNull(cause, "cause");
    Objects.requireNonNull(suppressed, "suppressed");
    Objects.requireNonNull(stackTrace, "stackTrace");
  }

  @Override
  public String toString()
  {
    final var builder =
      new StringBuilder(1024)
      .append(this.className)
      .append(':')
      .append(' ')
      .append(this.message)
      .append(System.lineSeparator());

    for (final var e : this.stackTrace) {
      builder.append("  at ");
      builder.append(e);
      builder.append(System.lineSeparator());
    }

    if (this.cause.isPresent()) {
      final var c = this.cause.get();
      builder.append("Caused by: ");
      builder.append(c);
    }

    for (final var s : this.suppressed) {
      builder.append("Suppressed: ");
      builder.append(s);
    }

    return builder.toString();
  }

  /**
   * Convert the given exception to a stored exception.
   *
   * @param e The exception
   *
   * @return A stored exception
   */

  public static NPStoredException ofException(
    final Throwable e)
  {
    return switch (e) {
      case final SStructuredErrorType<?> se -> {
        yield new NPStoredException(
          e.getClass().getCanonicalName(),
          Objects.requireNonNullElse(e.getMessage(), e.getClass().getName()),
          se.attributes(),
          Optional.ofNullable(e.getCause())
            .map(NPStoredException::ofException),
          Arrays.stream(e.getSuppressed())
            .map(NPStoredException::ofException)
            .toList(),
          Arrays.stream(e.getStackTrace())
            .map(NPStoredStackTraceElement::ofElement)
            .toList()
        );
      }
      default -> {
        yield new NPStoredException(
          e.getClass().getCanonicalName(),
          Objects.requireNonNullElse(e.getMessage(), e.getClass().getName()),
          Map.of(),
          Optional.ofNullable(e.getCause())
            .map(NPStoredException::ofException),
          Arrays.stream(e.getSuppressed())
            .map(NPStoredException::ofException)
            .toList(),
          Arrays.stream(e.getStackTrace())
            .map(NPStoredStackTraceElement::ofElement)
            .toList()
        );
      }
    };
  }
}
