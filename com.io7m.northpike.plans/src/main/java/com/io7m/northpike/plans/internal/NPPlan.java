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


package com.io7m.northpike.plans.internal;

import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.plans.NPPlanDependency;
import com.io7m.northpike.model.plans.NPPlanElementName;
import com.io7m.northpike.model.plans.NPPlanElementType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanTimeouts;
import com.io7m.northpike.model.plans.NPPlanType;
import org.jgrapht.Graph;

import java.util.Map;
import java.util.Objects;

/**
 * A plan.
 */

public final class NPPlan implements NPPlanType
{
  private final NPPlanIdentifier identifier;
  private final String description;
  private final NPPlanTimeouts timeouts;
  private final Map<NPToolReferenceName, NPToolReference> toolReferences;
  private final Map<NPPlanElementName, NPPlanElementType> elements;
  private final Graph<NPPlanElementType, NPPlanDependency> graph;

  NPPlan(
    final NPPlanIdentifier inIdentifier,
    final String inDescription,
    final NPPlanTimeouts inTimeouts,
    final Map<NPToolReferenceName, NPToolReference> inToolReferences,
    final Map<NPPlanElementName, NPPlanElementType> inElements,
    final Graph<NPPlanElementType, NPPlanDependency> inGraph)
  {
    this.identifier =
      Objects.requireNonNull(inIdentifier, "identifier");
    this.description =
      Objects.requireNonNull(inDescription, "description");
    this.timeouts =
      Objects.requireNonNull(inTimeouts, "timeouts");
    this.toolReferences =
      Objects.requireNonNull(inToolReferences, "toolReferences");
    this.elements =
      Objects.requireNonNull(inElements, "elements");
    this.graph =
      Objects.requireNonNull(inGraph, "graph");
  }

  @Override
  public NPPlanIdentifier identifier()
  {
    return this.identifier;
  }

  @Override
  public String description()
  {
    return this.description;
  }

  @Override
  public NPPlanTimeouts timeouts()
  {
    return this.timeouts;
  }

  @Override
  public Map<NPToolReferenceName, NPToolReference> toolReferences()
  {
    return this.toolReferences;
  }

  @Override
  public Map<NPPlanElementName, NPPlanElementType> elements()
  {
    return this.elements;
  }

  @Override
  public Graph<NPPlanElementType, NPPlanDependency> graph()
  {
    return this.graph;
  }

  @Override
  public String toString()
  {
    return "[Plan %s %s]"
      .formatted(
        this.identifier.name(),
        Long.toUnsignedString(this.identifier.version())
      );
  }
}
