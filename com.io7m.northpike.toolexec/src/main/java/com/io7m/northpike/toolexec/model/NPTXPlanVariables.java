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

import com.io7m.jaffirm.core.Preconditions;
import com.io7m.lanark.core.RDottedName;

import java.util.Map;
import java.util.Objects;

/**
 * The set of plan variables.
 *
 * @param variables The variables
 */

public record NPTXPlanVariables(
  Map<RDottedName, NPTXPlanVariableType> variables)
{
  /**
   * The set of plan variables.
   *
   * @param variables The variables
   */

  public NPTXPlanVariables
  {
    Objects.requireNonNull(variables, "variables");

    for (final var entry : variables.entrySet()) {
      final var name =
        entry.getKey();
      final var val =
        entry.getValue();

      Preconditions.checkPreconditionV(
        Objects.equals(name, val.name()),
        "Map key %s must match variable name %s",
        name,
        val.name()
      );
    }

    variables = Map.copyOf(variables);
  }
}
