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

import com.io7m.seltzer.api.SStructuredErrorExceptionType;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * The base type of exceptions.
 */

public class NPException extends Exception
  implements SStructuredErrorExceptionType<NPErrorCode>
{
  private final NPErrorCode errorCode;
  private final Map<String, String> attributes;
  private final Optional<String> remediatingAction;

  /**
   * Construct an exception.
   *
   * @param message             The message
   * @param inErrorCode         The error code
   * @param inAttributes        The error attributes
   * @param inRemediatingAction The remediating action, if any
   */

  public NPException(
    final String message,
    final NPErrorCode inErrorCode,
    final Map<String, String> inAttributes,
    final Optional<String> inRemediatingAction)
  {
    super(Objects.requireNonNull(message, "message"));

    this.errorCode =
      Objects.requireNonNull(inErrorCode, "errorCode");
    this.attributes =
      Objects.requireNonNull(inAttributes, "attributes");
    this.remediatingAction =
      Objects.requireNonNull(inRemediatingAction, "remediatingAction");
  }

  /**
   * Construct an exception.
   *
   * @param message             The message
   * @param cause               The cause
   * @param inErrorCode         The error code
   * @param inAttributes        The error attributes
   * @param inRemediatingAction The remediating action, if any
   */

  public NPException(
    final String message,
    final Throwable cause,
    final NPErrorCode inErrorCode,
    final Map<String, String> inAttributes,
    final Optional<String> inRemediatingAction)
  {
    super(
      Objects.requireNonNull(message, "message"),
      Objects.requireNonNull(cause, "cause")
    );
    this.errorCode =
      Objects.requireNonNull(inErrorCode, "errorCode");
    this.attributes =
      Objects.requireNonNull(inAttributes, "attributes");
    this.remediatingAction =
      Objects.requireNonNull(inRemediatingAction, "remediatingAction");
  }

  @Override
  public final NPErrorCode errorCode()
  {
    return this.errorCode;
  }

  @Override
  public final Map<String, String> attributes()
  {
    return this.attributes;
  }

  @Override
  public final Optional<String> remediatingAction()
  {
    return this.remediatingAction;
  }

  @Override
  public final Optional<Throwable> exception()
  {
    return Optional.of(this);
  }

  /**
   * Construct an exception from an existing exception.
   *
   * @param ex The cause
   *
   * @return The new exception
   */

  public static NPException ofException(
    final Throwable ex)
  {
    return switch (ex) {
      case final NPException e -> {
        yield e;
      }

      case final SStructuredErrorExceptionType<?> e -> {
        yield new NPException(
          e.getMessage(),
          ex,
          new NPErrorCode(e.errorCode().toString()),
          e.attributes(),
          e.remediatingAction()
        );
      }

      default -> {
        yield new NPException(
          Objects.requireNonNullElse(
            ex.getMessage(),
            ex.getClass().getSimpleName()),
          ex,
          NPStandardErrorCodes.errorIo(),
          Map.of(),
          Optional.empty()
        );
      }
    };
  }
}
