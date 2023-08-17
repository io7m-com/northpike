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


package com.io7m.northpike.plans.parsers;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.NPPlans;
import com.io7m.northpike.strings.NPStrings;

import java.util.Map;
import java.util.Objects;

/**
 * A raw, parsed description of a plan. There are no guarantees that this
 * constitutes a valid plan. The {@link #toPlan(NPStrings)} method will pass
 * the elements of this description through the usual plan builder, and this
 * will validate the plan and compile it into something executable.
 *
 * @param identifier     The plan identifier
 * @param toolReferences The tool references
 * @param elements       The plan elements
 */

public record NPPlanDescription(
  NPPlanIdentifier identifier,
  Map<RDottedName, NPToolReference> toolReferences,
  Map<NPPlanElementName, NPPlanElementDescriptionType> elements)
{
  /**
   * A raw, parsed description of a plan. There are no guarantees that this
   * constitutes a valid plan. The {@link #toPlan(NPStrings)} method will pass
   * the elements of this description through the usual plan builder, and this
   * will validate the plan and compile it into something executable.
   *
   * @param identifier     The plan identifier
   * @param toolReferences The tool references
   * @param elements       The plan elements
   */

  public NPPlanDescription
  {
    Objects.requireNonNull(identifier, "identifier");
    Objects.requireNonNull(toolReferences, "toolReferences");
    Objects.requireNonNull(elements, "elements");
  }

  /**
   * Convert this description into a plan, performing structural and validity
   * checks.
   *
   * @param strings The string resources
   *
   * @return The plan
   *
   * @throws NPPlanException On errors
   */

  public NPPlanType toPlan(
    final NPStrings strings)
    throws NPPlanException
  {
    final var builder =
      NPPlans.builder(
        strings,
        this.identifier.name().name().value(),
        this.identifier.version()
      );

    for (final var refs : this.toolReferences.values()) {
      builder.addToolReference(refs);
    }

    for (final var element : this.elements.values()) {
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
