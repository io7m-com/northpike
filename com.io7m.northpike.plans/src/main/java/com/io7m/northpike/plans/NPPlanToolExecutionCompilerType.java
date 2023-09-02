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

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.plans.variables.NPPlanVariables;
import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;

/**
 * An interface that can be used to compile tool executions for plans.
 */

public interface NPPlanToolExecutionCompilerType
{
  /**
   * Compile a tool execution for the given plan variables.
   *
   * @param execution     The tool execution
   * @param planVariables The plan variables
   *
   * @return A type-checked execution
   *
   * @throws NPException On errors
   */

  NPTXTypeChecked toolCompile(
    NPToolExecutionIdentifier execution,
    NPPlanVariables planVariables)
    throws NPException;
}
