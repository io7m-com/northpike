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

package com.io7m.northpike.plans.preparation;

import com.io7m.jdeferthrow.core.ExceptionTracker;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlanTaskType;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.variables.NPPlanStandardVariables;
import com.io7m.northpike.plans.variables.NPPlanVariableString;
import com.io7m.northpike.plans.variables.NPPlanVariableStringSet;
import com.io7m.northpike.plans.variables.NPPlanVariableType;
import com.io7m.northpike.plans.variables.NPPlanVariables;
import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Functions to prepare plans for execution.
 */

public final class NPPlanPreparation
  implements NPPlanPreparationType
{
  private final NPPlanType plan;
  private final NPPlanVariables variables;
  private final Map<NPPlanElementName, NPTXTypeChecked> toolsCompiled;

  private NPPlanPreparation(
    final NPPlanType inPlan,
    final NPPlanVariables inVariables,
    final Map<NPPlanElementName, NPTXTypeChecked> inToolsCompiled)
  {
    this.plan =
      Objects.requireNonNull(inPlan, "plan");
    this.variables =
      Objects.requireNonNull(inVariables, "variables");
    this.toolsCompiled =
      Map.copyOf(
        Objects.requireNonNull(inToolsCompiled, "toolsCompiled")
      );
  }

  /**
   * Prepare a plan for the given commit.
   *
   * @param resources The plan resource interface
   * @param commit    The commit
   * @param plan      The plan
   *
   * @return A prepared plan
   *
   * @throws NPPlanException On errors
   */

  public static NPPlanPreparationType forCommit(
    final NPPlanPreparationResourcesType resources,
    final NPCommit commit,
    final NPPlanType plan)
    throws NPPlanException
  {
    Objects.requireNonNull(resources, "resources");
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(plan, "plan");

    final var variables = new ArrayList<NPPlanVariableType>();
    variables.addAll(createVariablesForCommit(resources, commit));

    final var planVariables =
      NPPlanVariables.ofList(variables);
    final var toolsCompiled =
      new HashMap<NPPlanElementName, NPTXTypeChecked>();

    final var exceptions = new ExceptionTracker<NPPlanException>();
    for (final var element : plan.elements().values()) {
      try {
        if (element instanceof final NPPlanTaskType task) {
          final var toolExec =
            task.toolExecution();
          final NPTXTypeChecked toolCompiled =
            resources.toolCompile(toolExec.execution(), planVariables);
          toolsCompiled.put(task.name(), toolCompiled);
        }
      } catch (final NPPlanException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new NPPlanPreparation(plan, planVariables, toolsCompiled);
  }

  private static Collection<? extends NPPlanVariableType>
  createVariablesForCommit(
    final NPPlanPreparationResourcesType resources,
    final NPCommit commit)
    throws NPPlanException
  {
    final var archive = resources.archiveForCommit(commit);
    return List.of(
      new NPPlanVariableString(
        NPPlanStandardVariables.archiveURL().name(),
        archive.sources().toString()
      ),
      new NPPlanVariableString(
        NPPlanStandardVariables.archiveChecksumURL().name(),
        archive.checksum().toString()
      ),
      new NPPlanVariableString(
        NPPlanStandardVariables.scmCommit().name(),
        commit.id().value()
      ),
      new NPPlanVariableStringSet(
        NPPlanStandardVariables.scmBranches().name(),
        commit.branches()
      )
    );
  }

  @Override
  public NPPlanVariables planVariables()
  {
    return this.variables;
  }

  @Override
  public NPPlanType plan()
  {
    return this.plan;
  }

  @Override
  public Map<NPPlanElementName, NPTXTypeChecked> toolExecutions()
  {
    return this.toolsCompiled;
  }
}
