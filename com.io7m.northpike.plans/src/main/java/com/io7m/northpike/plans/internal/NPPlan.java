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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.plans.NPPlanDependency;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanElementType;
import com.io7m.northpike.plans.NPPlanName;
import com.io7m.northpike.plans.NPPlanType;
import org.jgrapht.Graph;

import java.util.Map;
import java.util.Objects;

/**
 * A plan.
 */

public final class NPPlan implements NPPlanType
{
  private final NPPlanName name;
  private final long version;
  private final Map<RDottedName, NPToolReference> toolReferences;
  private final Map<NPPlanElementName, NPPlanElementType> elements;
  private final Graph<NPPlanElementType, NPPlanDependency> graph;

  NPPlan(
    final NPPlanName inName,
    final long inVersion,
    final Map<RDottedName, NPToolReference> inToolReferences,
    final Map<NPPlanElementName, NPPlanElementType> inElements,
    final Graph<NPPlanElementType, NPPlanDependency> inGraph)
  {
    this.name =
      Objects.requireNonNull(inName, "name");
    this.version =
      inVersion;
    this.toolReferences =
      Objects.requireNonNull(inToolReferences, "toolReferences");
    this.elements =
      Objects.requireNonNull(inElements, "elements");
    this.graph =
      Objects.requireNonNull(inGraph, "graph");
  }

  @Override
  public NPPlanName name()
  {
    return this.name;
  }

  @Override
  public long version()
  {
    return this.version;
  }

  @Override
  public Map<RDottedName, NPToolReference> toolReferences()
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
      .formatted(this.name, Long.toUnsignedString(this.version));
  }
}
