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


package com.io7m.northpike.shell.commons;

import com.io7m.repetoir.core.RPServiceType;
import org.jline.terminal.Terminal;

import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Shell options.
 */

public final class NPShellOptions
  implements RPServiceType
{
  private final AtomicBoolean terminateOnErrors;
  private NPFormatterType formatter;

  /**
   * Shell options.
   *
   * @param inTerminal The terminal
   */

  public NPShellOptions(
    final Terminal inTerminal)
  {
    this.terminateOnErrors =
      new AtomicBoolean(false);
    this.formatter =
      new NPFormatterPretty(inTerminal);
  }

  /**
   * @return A flag indicating if the shell should exit on errors
   */

  public AtomicBoolean terminateOnErrors()
  {
    return this.terminateOnErrors;
  }

  /**
   * Set the formatter.
   *
   * @param inFormatter The formatter
   */

  public void setFormatter(
    final NPFormatterType inFormatter)
  {
    this.formatter =
      Objects.requireNonNull(inFormatter, "formatter");
  }

  /**
   * @return The shell formatter
   */

  public NPFormatterType formatter()
  {
    return this.formatter;
  }

  @Override
  public String toString()
  {
    return "[%s]".formatted(this.getClass().getSimpleName());
  }

  @Override
  public String description()
  {
    return "Shell options service.";
  }
}
