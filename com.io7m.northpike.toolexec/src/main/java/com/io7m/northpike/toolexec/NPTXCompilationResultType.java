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

import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;

import java.util.List;
import java.util.Objects;

/**
 * The result of compiling a tool execution description.
 */

public sealed interface NPTXCompilationResultType
{
  /**
   * Compilation failed.
   *
   * @param messages The compilation messages
   */

  record Failure(
    List<NPCompilationMessage> messages)
    implements NPTXCompilationResultType
  {
    /**
     * Compilation failed.
     */

    public Failure
    {
      Objects.requireNonNull(messages, "messages");
    }
  }

  /**
   * Compilation succeeded.
   *
   * @param checked The type-checked result
   */

  record Success(
    NPTXTypeChecked checked)
    implements NPTXCompilationResultType
  {
    /**
     * Compilation succeeded.
     */

    public Success
    {
      Objects.requireNonNull(checked, "checked");
    }
  }
}
