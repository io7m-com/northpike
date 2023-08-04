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
import com.io7m.northpike.model.NPAgentLabelMatchType;

/**
 * A mutable builder for tasks.
 */

public interface NPPlanTaskBuilderType
  extends NPPlanElementBuilderType
{
  @Override
  NPPlanTaskBuilderType addDependsOn(
    RDottedName target)
    throws NPPlanException;

  @Override
  NPPlanTaskBuilderType setDescription(
    String description)
    throws NPPlanException;

  /**
   * Set the expression against which agents will be required to match.
   *
   * @param match The expression
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType setAgentRequireWithLabels(
    NPAgentLabelMatchType match)
    throws NPPlanException;

  /**
   * Set the expression against which agents will be preferred to match.
   *
   * @param match The expression
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType setAgentPreferWithLabels(
    NPAgentLabelMatchType match)
    throws NPPlanException;

  /**
   * Add a resource that will be locked on the agent during execution of this
   * task.
   *
   * @param name The resource name
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType addLockAgentResource(
    RDottedName name)
    throws NPPlanException;

  /**
   * Set the tool execution for this task.
   *
   * @param toolExecution The tool execution
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType setToolExecution(
    NPPlanToolExecution toolExecution)
    throws NPPlanException;
}
