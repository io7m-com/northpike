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

import java.util.Objects;

/**
 * The compilation message.
 *
 * @param kind    The message kind
 * @param line    The line number
 * @param column  The column number
 * @param message The message
 */

public record NPCompilationMessage(
  Kind kind,
  int line,
  int column,
  String message)
{
  /**
   * The compilation message.
   *
   * @param kind    The message kind
   * @param line    The line number
   * @param column  The column number
   * @param message The message
   */

  public NPCompilationMessage
  {
    Objects.requireNonNull(kind, "kind");
    Objects.requireNonNull(message, "message");
  }

  /**
   * The kind of message.
   */

  public enum Kind
  {
    /**
     * The message is info.
     */

    INFO,

    /**
     * The message is a warning.
     */

    WARNING,

    /**
     * The message is an error.
     */

    ERROR
  }
}
