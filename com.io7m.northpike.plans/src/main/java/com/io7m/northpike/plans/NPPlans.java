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

import com.io7m.northpike.model.plans.NPPlanBarrierDescription;
import com.io7m.northpike.model.plans.NPPlanBuilderType;
import com.io7m.northpike.model.plans.NPPlanDescription;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.model.plans.NPPlanTaskDescription;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.internal.NPPlanBuilder;
import com.io7m.northpike.strings.NPStrings;

/**
 * Functions to construct plans.
 */

public final class NPPlans
{
  private NPPlans()
  {

  }

  /**
   * Create a new plan builder.
   *
   * @param strings The string resources
   * @param name    The plan name
   * @param version The plan version
   *
   * @return A new plan builder
   */

  public static NPPlanBuilderType builder(
    final NPStrings strings,
    final NPPlanName name,
    final long version)
  {
    return new NPPlanBuilder(strings, new NPPlanIdentifier(name, version));
  }

  /**
   * Create a new plan builder.
   *
   * @param strings The string resources
   * @param name    The plan name
   * @param version The plan version
   *
   * @return A new plan builder
   */

  public static NPPlanBuilderType builder(
    final NPStrings strings,
    final String name,
    final long version)
  {
    return builder(strings, NPPlanName.of(name), version);
  }

  /**
   * Convert a description into a plan, performing structural and validity
   * checks.
   *
   * @param description The plan description
   * @param strings     The string resources
   *
   * @return The plan
   *
   * @throws NPPlanException On errors
   */

  public static NPPlanType toPlan(
    final NPPlanDescription description,
    final NPStrings strings)
    throws NPPlanException
  {
    final var builder =
      NPPlans.builder(
        strings,
        description.identifier().name().name().value(),
        description.identifier().version()
      );

    builder.setTimeouts(description.timeouts());
    builder.setDescription(description.description());

    for (final var refs : description.toolReferences().values()) {
      builder.addToolReference(refs);
    }

    for (final var element : description.elements().values()) {
      if (element instanceof final NPPlanTaskDescription task) {
        task.toTask(builder.addTask(task.name()));
        continue;
      }
      if (element instanceof final NPPlanBarrierDescription barrier) {
        barrier.toBarrier(builder.addBarrier(barrier.name()));
        continue;
      }
    }

    return builder.build();
  }
}
