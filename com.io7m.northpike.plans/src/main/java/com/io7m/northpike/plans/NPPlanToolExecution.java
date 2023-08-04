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


package com.io7m.northpike.plans;

import com.io7m.lanark.core.RDottedName;

import java.util.Objects;
import java.util.Set;

/**
 * A tool execution.
 *
 * @param name             The name of the tool
 * @param argument         The name of the argument
 * @param toolRequirements The required tools
 */

public record NPPlanToolExecution(
  RDottedName name,
  RDottedName argument,
  Set<RDottedName> toolRequirements)
{
  /**
   * A tool execution.
   *
   * @param name             The name of the tool
   * @param argument         The name of the argument
   * @param toolRequirements The required tools
   */

  public NPPlanToolExecution
  {
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(argument, "argument");
    Objects.requireNonNull(toolRequirements, "toolRequirements");
  }
}
