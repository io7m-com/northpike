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


package com.io7m.northpike.plans.analysis;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.Anything;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsEqualTo;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsNotEqualTo;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsOverlapping;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsSubsetOf;
import com.io7m.northpike.model.comparisons.NPComparisonSetType.IsSupersetOf;
import com.io7m.northpike.model.plans.NPPlanBarrierType;
import com.io7m.northpike.model.plans.NPPlanElementName;
import com.io7m.northpike.model.plans.NPPlanException;
import com.io7m.northpike.model.plans.NPPlanTaskType;
import com.io7m.northpike.model.plans.NPPlanType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluation;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementBecameReady;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresMatchingAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresSpecificAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentAcceptedTask;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskSuccess;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.northpike.strings.NPStrings;

import java.time.Clock;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.UUID;
import java.util.stream.Collectors;

import static com.io7m.northpike.strings.NPStringConstantApplied.applied;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_ANY_LABEL;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_DONE;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_EMPTY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_LABEL_IS_EQUAL_TO;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_LABEL_IS_NOT_EQUAL_TO;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_LABEL_OVERLAPPING;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_LABEL_SUBSET;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_LABEL_SUPERSET;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_AGENT_TIMEOUT;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_EXECUTION_TIMEOUT;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT;
import static com.io7m.northpike.strings.NPStringConstants.PLAN_EXPLAIN_TASK_REQUIRES_SPECIFIC_AGENT;
import static java.time.ZoneOffset.UTC;

/**
 * Functions to explain plans.
 */

public final class NPPlanExplanation implements NPPlanExplanationType
{
  private final List<NPStringConstantType> messages;

  private NPPlanExplanation(
    final ArrayList<NPStringConstantType> inMessages)
  {
    this.messages = List.copyOf(inMessages);
  }

  /**
   * Explain the given plan.
   *
   * @param strings The string resources
   * @param plan    The plan
   *
   * @return An explanation
   *
   * @throws NPPlanException On errors
   */

  public static NPPlanExplanationType explain(
    final NPStrings strings,
    final NPPlanType plan)
    throws NPPlanException
  {
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(plan, "plan");

    try {
      final var evaluation =
        NPPlanEvaluation.create(Clock.fixed(Instant.EPOCH, UTC), plan);

      final var updates =
        new ArrayList<NPPlanEvaluationUpdateType>();
      final var updatesNext =
        new ArrayList<NPPlanEvaluationUpdateType>();
      final var messages =
        new ArrayList<NPStringConstantType>();

      NPPlanEvaluationStatusType status;

      if (plan.elements().isEmpty()) {
        messages.add(PLAN_EXPLAIN_EMPTY);
        return new NPPlanExplanation(messages);
      }

      int steps = 0;
      while (true) {
        status = evaluation.step(updates);
        if (status.isTerminal()) {
          break;
        }

        updates.addAll(updatesNext);
        updatesNext.clear();

        evaluateStatus(
          strings,
          updates,
          updatesNext,
          messages,
          status
        );

        ++steps;
      }

      messages.add(PLAN_EXPLAIN_DONE);
      return new NPPlanExplanation(messages);
    } catch (final NPException e) {
      throw new NPPlanException(
        e.getMessage(),
        e,
        e.errorCode(),
        e.attributes(),
        e.remediatingAction()
      );
    }
  }

  private static void evaluateStatus(
    final NPStrings strings,
    final ArrayList<NPPlanEvaluationUpdateType> updates,
    final ArrayList<NPPlanEvaluationUpdateType> updatesNext,
    final ArrayList<NPStringConstantType> messages,
    final NPPlanEvaluationStatusType status)
    throws NPException
  {
    for (final var event : status.events()) {
      if (event instanceof final ElementBecameReady e) {
        if (e.element() instanceof final NPPlanTaskType t) {
          if (t.dependsOn().isEmpty()) {
            messages.add(
              applied(PLAN_EXPLAIN_TASK_BECOMES_READY_EMPTY, t.name())
            );
          } else {
            final var dependencies =
              t.dependsOn()
                .stream()
                .map(NPPlanElementName::toString)
                .collect(Collectors.joining(", "));

            messages.add(
              applied(
                PLAN_EXPLAIN_TASK_BECOMES_READY_DEPENDENCIES,
                dependencies,
                t.name()
              )
            );
          }
          continue;
        }

        if (e.element() instanceof final NPPlanBarrierType b) {
          if (b.dependsOn().isEmpty()) {
            messages.add(
              applied(PLAN_EXPLAIN_BARRIER_BECOMES_READY_EMPTY, b.name())
            );
          } else {
            final var dependencies =
              b.dependsOn()
                .stream()
                .map(NPPlanElementName::toString)
                .collect(Collectors.joining(", "));

            messages.add(
              applied(
                PLAN_EXPLAIN_BARRIER_BECOMES_READY_DEPENDENCIES,
                dependencies,
                b.name()
              )
            );
          }
          continue;
        }
      }

      if (event instanceof final TaskRequiresMatchingAgent e) {
        final var task =
          e.task();
        final var agent =
          new NPAgentID(UUID.randomUUID());

        messages.add(
          applied(
            PLAN_EXPLAIN_TASK_REQUIRES_MATCHING_AGENT,
            task.name(),
            agent,
            serializeToString(strings, task.agentRequireWithLabel())
          )
        );

        task.agentSelectionTimeout().ifPresent(duration -> {
          messages.add(
            applied(
              PLAN_EXPLAIN_TASK_AGENT_TIMEOUT,
              task.name(),
              duration
            )
          );
        });

        task.executionTimeout().ifPresent(duration -> {
          messages.add(
            applied(
              PLAN_EXPLAIN_TASK_EXECUTION_TIMEOUT,
              task.name(),
              duration
            )
          );
        });

        updates.add(new AgentAcceptedTask(task.name(), agent));
        updatesNext.add(new AgentReportedTaskSuccess(task.name(), agent));
        continue;
      }

      if (event instanceof final TaskRequiresSpecificAgent e) {
        final var task =
          e.task();
        final var agent =
          e.agent();

        final var previousTask =
          task.agentMustBeSameAs()
            .orElseThrow()
            .name();

        messages.add(
          applied(
            PLAN_EXPLAIN_TASK_REQUIRES_SPECIFIC_AGENT,
            task.name(),
            agent,
            previousTask
          )
        );

        task.agentSelectionTimeout().ifPresent(duration -> {
          messages.add(
            applied(
              PLAN_EXPLAIN_TASK_AGENT_TIMEOUT,
              task.name(),
              duration
            )
          );
        });

        task.executionTimeout().ifPresent(duration -> {
          messages.add(
            applied(
              PLAN_EXPLAIN_TASK_EXECUTION_TIMEOUT,
              task.name(),
              duration
            )
          );
        });

        updates.add(new AgentAcceptedTask(task.name(), agent));
        updatesNext.add(new AgentReportedTaskSuccess(task.name(), agent));
        continue;
      }
    }
  }

  private static String serializeToString(
    final NPStrings strings,
    final NPComparisonSetType<NPAgentLabelName> comparison)
  {
    if (comparison instanceof Anything<NPAgentLabelName>) {
      return strings.format(PLAN_EXPLAIN_ANY_LABEL);
    }
    if (comparison instanceof final IsSupersetOf<NPAgentLabelName> e) {
      return strings.format(PLAN_EXPLAIN_LABEL_SUPERSET, e.value());
    }
    if (comparison instanceof final IsSubsetOf<NPAgentLabelName> e) {
      return strings.format(PLAN_EXPLAIN_LABEL_SUBSET, e.value());
    }
    if (comparison instanceof final IsOverlapping<NPAgentLabelName> e) {
      return strings.format(PLAN_EXPLAIN_LABEL_OVERLAPPING, e.value());
    }
    if (comparison instanceof final IsEqualTo<NPAgentLabelName> e) {
      return strings.format(PLAN_EXPLAIN_LABEL_IS_EQUAL_TO, e.value());
    }
    if (comparison instanceof final IsNotEqualTo<NPAgentLabelName> e) {
      return strings.format(PLAN_EXPLAIN_LABEL_IS_NOT_EQUAL_TO, e.value());
    }
    throw new IllegalStateException("Unrecognized comparison: " + comparison);
  }

  @Override
  public List<NPStringConstantType> messages()
  {
    return List.copyOf(this.messages);
  }
}
