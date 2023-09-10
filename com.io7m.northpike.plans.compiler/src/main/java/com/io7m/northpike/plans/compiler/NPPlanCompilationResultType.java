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


package com.io7m.northpike.plans.compiler;

import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.plans.NPPlanType;

import java.util.List;
import java.util.Objects;

/**
 * The result of compiling a plan.
 */

public sealed interface NPPlanCompilationResultType
{
  /**
   * Compilation failed.
   *
   * @param messages The compilation messages
   */

  record Failure(
    List<NPCompilationMessage> messages)
    implements NPPlanCompilationResultType
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
   * @param plan The compiled result
   */

  record Success(
    NPPlanType plan)
    implements NPPlanCompilationResultType
  {
    /**
     * Compilation succeeded.
     */

    public Success
    {
      Objects.requireNonNull(plan, "checked");
    }
  }
}
