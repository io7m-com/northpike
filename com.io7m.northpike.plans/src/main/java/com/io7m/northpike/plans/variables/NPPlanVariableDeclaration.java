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


package com.io7m.northpike.plans.variables;

import com.io7m.lanark.core.RDottedName;

import java.util.Objects;

/**
 * The declaration of a variable.
 *
 * @param type        The variable type
 * @param name        The variable name
 * @param description A humanly-readable description of the variable
 * @param <T>         The variable type
 */

public record NPPlanVariableDeclaration<T extends NPPlanVariableType>(
  Class<T> type,
  RDottedName name,
  String description)
{
  /**
   * The declaration of a variable.
   *
   * @param type        The variable type
   * @param name        The variable name
   * @param description A humanly-readable description of the variable
   */

  public NPPlanVariableDeclaration
  {
    Objects.requireNonNull(type, "type");
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(description, "description");
  }
}
