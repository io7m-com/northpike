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


package com.io7m.northpike.model.plans;

import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import org.jgrapht.Graph;

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * An execution plan.
 */

public interface NPPlanType
{
  /**
   * @return The plan identifier
   */

  NPPlanIdentifier identifier();

  /**
   * @return A humanly-readable plan description
   */

  String description();

  /**
   * @return The default plan timeouts
   */

  NPPlanTimeouts timeouts();

  /**
   * @return The tools to which this plan refers
   */

  Map<NPToolReferenceName, NPToolReference> toolReferences();

  /**
   * @return The execution elements in this plan
   */

  Map<NPPlanElementName, NPPlanElementType> elements();

  /**
   * @return The execution graph for this plan
   */

  Graph<NPPlanElementType, NPPlanDependency> graph();

  /**
   * @return The plan summary
   */

  default NPPlanSummary summary()
  {
    return new NPPlanSummary(this.identifier(), this.description());
  }

  /**
   * @return The set of tool executions upon which this plan depends
   */

  default Set<NPToolExecutionIdentifier> toolExecutions()
  {
    return this.elements()
      .values()
      .stream()
      .flatMap(e -> {
        if (e instanceof final NPPlanTaskType task) {
          return Stream.of(task.toolExecution().execution());
        }
        return Stream.of();
      })
      .collect(Collectors.toUnmodifiableSet());
  }
}
