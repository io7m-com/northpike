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

import com.io7m.northpike.model.NPToolReference;

/**
 * A mutable builder for plans.
 */

public interface NPPlanBuilderType
{
  /**
   * Set the plan description.
   *
   * @param description The description
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanBuilderType setDescription(
    String description)
    throws NPPlanException;

  /**
   * Construct a plan.
   *
   * @return A plan based on all the given information
   *
   * @throws NPPlanException On errors
   */

  NPPlanType build()
    throws NPPlanException;

  /**
   * Set the default plan timeouts.
   *
   * @param timeouts The timeouts
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanBuilderType setTimeouts(
    NPPlanTimeouts timeouts)
    throws NPPlanException;

  /**
   * Add a tool reference.
   *
   * @param reference The reference
   *
   * @return this
   *
   * @throws NPPlanException On errors
   */

  NPPlanBuilderType addToolReference(
    NPToolReference reference)
    throws NPPlanException;

  /**
   * Add a barrier.
   *
   * @param name The name of the barrier
   *
   * @return A barrier builder
   *
   * @throws NPPlanException On errors
   */

  NPPlanBarrierBuilderType addBarrier(
    NPPlanElementName name)
    throws NPPlanException;

  /**
   * Add a barrier.
   *
   * @param name The name of the barrier
   *
   * @return A barrier builder
   *
   * @throws NPPlanException On errors
   */

  default NPPlanBarrierBuilderType addBarrier(
    final String name)
    throws NPPlanException
  {
    return this.addBarrier(NPPlanElementName.of(name));
  }

  /**
   * Add a task.
   *
   * @param name The name of the task
   *
   * @return A task builder
   *
   * @throws NPPlanException On errors
   */

  NPPlanTaskBuilderType addTask(
    NPPlanElementName name)
    throws NPPlanException;

  /**
   * Add a task.
   *
   * @param name The name of the task
   *
   * @return A task builder
   *
   * @throws NPPlanException On errors
   */

  default NPPlanTaskBuilderType addTask(
    final String name)
    throws NPPlanException
  {
    return this.addTask(NPPlanElementName.of(name));
  }
}
