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


package com.io7m.northpike.toolexec.model;

import com.io7m.jlexing.core.LexicalPosition;

import java.net.URI;
import java.util.List;
import java.util.Objects;

/**
 * A conditional statement. If the given condition evaluates to true, the
 * statements in the true branch are executed. Otherwise, the statements in
 * the false branch are executed.
 *
 * @param lexical     The lexical position of the statement
 * @param condition   The condition expression
 * @param branchTrue  The true branch
 * @param branchFalse The false branch
 */

public record NPTXSIf(
  LexicalPosition<URI> lexical,
  NPTXExpressionType condition,
  List<NPTXStatementType> branchTrue,
  List<NPTXStatementType> branchFalse)
  implements NPTXStatementType
{
  /**
   * A conditional statement. If the given condition evaluates to true, the
   * statements in the true branch are executed. Otherwise, the statements in
   * the false branch are executed.
   *
   * @param lexical     The lexical position of the statement
   * @param condition   The condition expression
   * @param branchTrue  The true branch
   * @param branchFalse The false branch
   */

  public NPTXSIf
  {
    Objects.requireNonNull(lexical, "lexical");
    Objects.requireNonNull(condition, "condition");
    Objects.requireNonNull(branchFalse, "branchFalse");
    Objects.requireNonNull(branchTrue, "branchTrue");
  }
}
