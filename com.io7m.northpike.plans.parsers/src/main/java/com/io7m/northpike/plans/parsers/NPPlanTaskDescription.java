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
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanException;
import com.io7m.northpike.plans.NPPlanTaskBuilderType;
import com.io7m.northpike.plans.NPPlanToolExecution;

import java.time.Duration;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * A raw, parsed task description.
 *
 * @param name                   The task name
 * @param description            The task description
 * @param agentRequireWithLabel  The "require agent" expression
 * @param agentPreferWithLabel   The "prefer agent" expression
 * @param agentMustBeSameAs      The "same as" agent constraint
 * @param agentAssignmentTimeout The timeout value for assignment
 * @param executionTimeout       The execution timeout
 * @param lockAgentResources     The resources locked on the agent
 * @param toolExecution          The tool execution
 * @param dependsOn              The tasks/barriers upon which this task depends
 */

public record NPPlanTaskDescription(
  NPPlanElementName name,
  String description,
  NPAgentLabelMatchType agentRequireWithLabel,
  NPAgentLabelMatchType agentPreferWithLabel,
  Optional<RDottedName> agentMustBeSameAs,
  Optional<Duration> agentAssignmentTimeout,
  Optional<Duration> executionTimeout,
  Set<RDottedName> lockAgentResources,
  NPPlanToolExecution toolExecution,
  Set<RDottedName> dependsOn)
  implements NPPlanElementDescriptionType
{
  /**
   * A raw, parsed task description.
   *
   * @param name                   The task name
   * @param description            The task description
   * @param agentRequireWithLabel  The "require agent" expression
   * @param agentPreferWithLabel   The "prefer agent" expression
   * @param agentMustBeSameAs      The "same as" agent constraint
   * @param agentAssignmentTimeout The timeout value for assignment
   * @param executionTimeout       The execution timeout
   * @param lockAgentResources     The resources locked on the agent
   * @param toolExecution          The tool execution
   * @param dependsOn              The tasks/barriers upon which this task depends
   */

  public NPPlanTaskDescription
  {
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(description, "description");
    Objects.requireNonNull(agentRequireWithLabel, "agentRequireWithLabel");
    Objects.requireNonNull(agentPreferWithLabel, "agentPreferWithLabel");
    Objects.requireNonNull(agentMustBeSameAs, "agentMustBeSameAs");
    Objects.requireNonNull(agentAssignmentTimeout, "agentAssignmentTimeout");
    Objects.requireNonNull(executionTimeout, "executionTimeout");
    Objects.requireNonNull(lockAgentResources, "lockAgentResources");
    Objects.requireNonNull(toolExecution, "toolExecution");
    Objects.requireNonNull(dependsOn, "dependsOn");
  }

  /**
   * Convert this description to a task using the given task builder.
   *
   * @param taskBuilder The builder
   *
   * @throws NPPlanException On errors
   */

  public void toTask(
    final NPPlanTaskBuilderType taskBuilder)
    throws NPPlanException
  {
    taskBuilder.setDescription(this.description);
    taskBuilder.setAgentRequireWithLabels(this.agentRequireWithLabel);
    taskBuilder.setAgentPreferWithLabels(this.agentPreferWithLabel);

    if (this.agentMustBeSameAs.isPresent()) {
      final var same = this.agentMustBeSameAs.get();
      taskBuilder.setAgentMustBeSameAs(new NPPlanElementName(same));
    }
    if (this.agentAssignmentTimeout.isPresent()) {
      taskBuilder.setAgentAssignmentTimeout(this.agentAssignmentTimeout.get());
    }
    if (this.executionTimeout.isPresent()) {
      taskBuilder.setExecutionTimeout(this.executionTimeout.get());
    }
    for (final var lock : this.lockAgentResources) {
      taskBuilder.addLockAgentResource(lock);
    }
    taskBuilder.setToolExecution(this.toolExecution);

    for (final var depends : this.dependsOn) {
      taskBuilder.addDependsOn(new NPPlanElementName(depends));
    }
  }
}
