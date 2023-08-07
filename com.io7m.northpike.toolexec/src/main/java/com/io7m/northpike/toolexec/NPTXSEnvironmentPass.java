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


package com.io7m.northpike.toolexec;

import com.io7m.jlexing.core.LexicalPosition;

import java.net.URI;
import java.util.Objects;

/**
 * A statement that ensures an environment variable will be passed from the
 * agent's environment to the environment of the tool execution.
 *
 * @param lexical The lexical position of the statement
 * @param name    The name of the variable
 */

public record NPTXSEnvironmentPass(
  LexicalPosition<URI> lexical,
  String name)
  implements NPTXStatementType
{
  /**
   * A statement that ensures an environment variable will be passed from the
   * agent's environment to the environment of the tool execution.
   *
   * @param lexical The lexical position of the statement
   * @param name    The name of the variable
   */

  public NPTXSEnvironmentPass
  {
    Objects.requireNonNull(lexical, "lexical");
    Objects.requireNonNull(name, "value");
  }
}
