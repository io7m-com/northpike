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

import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPAgentResourceName;

import java.time.Duration;

/**
 * A mutable builder for tasks.
 */

public interface NPPlanTaskBuilderType
  extends NPPlanElementBuilderType
{
  @Override
  NPPlanTaskBuilderType addDependsOn(
    NPPlanElementName target)
    throws NPPlanException;

  /**
   * Add a dependency on another element.
   *
   * @param target The target element
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  default NPPlanTaskBuilderType addDependsOn(
    final String target)
    throws NPPlanException
  {
    return this.addDependsOn(NPPlanElementName.of(target));
  }

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
   * Set a constraint that indicates that this task must be executed by the
   * same agent that executed the given task. This adds an implicit execution
   * dependency on the given task; this method behaves as if
   * {@link #addDependsOn(NPPlanElementName)}
   * had been called on the given task.
   *
   * @param task The first task
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  default NPPlanTaskBuilderType setAgentMustBeSameAs(
    NPPlanTaskBuilderType task)
    throws NPPlanException
  {
    return this.setAgentMustBeSameAs(task.name());
  }

  /**
   * Set a constraint that indicates that this task must be executed by the
   * same agent that executed the given task. This adds an implicit execution
   * dependency on the given task; this method behaves as if
   * {@link #addDependsOn(NPPlanElementName)}
   * had been called on the given task.
   *
   * @param task The first task
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType setAgentMustBeSameAs(
    NPPlanElementName task)
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
    NPAgentResourceName name)
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

  /**
   * Set the maximum duration that the task will wait between the task
   * becoming ready, and having an agent selected. If this duration elapses
   * without an agent selected, the task will be considered failed.
   *
   * @param duration The timeout duration
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType setAgentSelectionTimeout(
    Duration duration)
    throws NPPlanException;

  /**
   * Set the maximum duration that the task will be allowed to execute.
   * If this duration elapses without the task being reported as either
   * having succeeded or failed, the task will be considered failed.
   *
   * @param duration The timeout duration
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType setExecutionTimeout(
    Duration duration)
    throws NPPlanException;
}
