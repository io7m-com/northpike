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


package com.io7m.northpike.plans.evaluation;

import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.plans.NPPlanBarrierType;
import com.io7m.northpike.plans.NPPlanDependency;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanElementType;
import com.io7m.northpike.plans.NPPlanTaskType;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementBecameReady;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskAgentAssignmentTimedOut;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskExecutionTimedOut;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresMatchingAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresSpecificAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusInProgress;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentAcceptedTask;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskFailure;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationUpdateType.AgentReportedTaskSuccess;
import org.jgrapht.Graph;
import org.jgrapht.traverse.TopologicalOrderIterator;

import java.time.Clock;
import java.time.Duration;
import java.time.Instant;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.FAILED;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.FAILED_TIMED_OUT_EXECUTION;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.IN_PROGRESS_EXECUTING;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.IN_PROGRESS_WAITING_NOT_READY;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.IN_PROGRESS_WAITING_READY;
import static com.io7m.northpike.plans.evaluation.NPPlanElementStatus.SUCEEDED;

/**
 * The plan evaluation function.
 */

public final class NPPlanEvaluation
  implements NPPlanEvaluationType
{
  private final Clock clock;
  private final NPPlanType plan;
  private final Set<NPPlanElementType> terminals;
  private final Graph<NPPlanElementType, NPPlanDependency> graph;
  private final LinkedList<NPPlanEvaluationEventType> stepEvents;
  private final Map<NPPlanElementName, ElementState> elements;

  private static final class ElementState
  {
    private final NPPlanElementType element;
    private Instant timeFinished;
    private Instant timeStartReady;
    private Instant timeStartWaitAgent;
    private Instant timeStartExecute;
    private NPPlanElementStatus status;
    private Optional<NPAgentID> agent;

    ElementState(
      final Clock clock,
      final NPPlanElementType inElement)
    {
      this.element = inElement;
      this.status = IN_PROGRESS_WAITING_NOT_READY;
      this.agent = Optional.empty();

      this.timeStartReady = clock.instant();
      this.timeStartWaitAgent = clock.instant();
      this.timeStartExecute = clock.instant();
      this.timeFinished = clock.instant();
    }
  }

  private NPPlanEvaluation(
    final Clock inClock,
    final NPPlanType inPlan)
  {
    this.clock =
      Objects.requireNonNull(inClock, "clock");
    this.plan =
      Objects.requireNonNull(inPlan, "plan");

    this.graph =
      this.plan.graph();

    this.terminals =
      this.graph.vertexSet()
        .stream()
        .filter(e -> this.graph.inDegreeOf(e) == 0)
        .collect(Collectors.toUnmodifiableSet());

    this.elements = new HashMap<>();
    for (final var e : this.graph.vertexSet()) {
      this.elements.put(e.name(), new ElementState(inClock, e));
    }

    this.stepEvents =
      new LinkedList<>();
  }

  /**
   * Create a new plan evaluation.
   *
   * @param clock The clock
   * @param plan  The plan
   *
   * @return The evaluation
   */

  public static NPPlanEvaluationType create(
    final Clock clock,
    final NPPlanType plan)
  {
    return new NPPlanEvaluation(clock, plan);
  }

  @Override
  public NPPlanEvaluationStatusType step(
    final List<NPPlanEvaluationUpdateType> updates)
  {
    Objects.requireNonNull(updates, "updates");

    this.stepEvents.clear();

    if (this.isFailed()) {
      return new StatusFailed(List.copyOf(this.stepEvents));
    }

    if (this.isSucceeded()) {
      return new StatusSucceeded(List.copyOf(this.stepEvents));
    }

    this.evaluateUpdates(updates);
    this.evaluateElements();

    return new StatusInProgress(List.copyOf(this.stepEvents));
  }

  private void evaluateUpdates(
    final List<NPPlanEvaluationUpdateType> updates)
  {
    for (final var update : updates) {
      this.evaluateUpdate(update);
    }
  }

  private void evaluateUpdate(
    final NPPlanEvaluationUpdateType update)
  {
    if (update instanceof final AgentAcceptedTask accepted) {
      final var state = this.elements.get(accepted.task());
      state.status = IN_PROGRESS_EXECUTING;
      state.timeStartExecute = this.clock.instant();
      state.agent = Optional.of(accepted.agent());
      return;
    }

    if (update instanceof final AgentReportedTaskSuccess success) {
      final var state = this.elements.get(success.task());
      state.status = SUCEEDED;
      state.timeFinished = this.clock.instant();
      this.stepEvents.add(new ElementSucceeded(state.element));
      return;
    }

    if (update instanceof final AgentReportedTaskFailure failure) {
      final var state = this.elements.get(failure.task());
      state.status = FAILED;
      state.timeFinished = this.clock.instant();
      this.stepEvents.add(new ElementFailed(state.element));
      return;
    }
  }

  private void evaluateElements()
  {
    final var topo =
      new TopologicalOrderIterator<>(this.graph);

    while (topo.hasNext()) {
      final var element =
        topo.next();
      final var state =
        this.elements.get(element.name());

      switch (state.status) {
        case IN_PROGRESS_WAITING_NOT_READY -> {
          this.evaluateElementWaitingNotReady(state);
        }
        case IN_PROGRESS_WAITING_READY -> {
          this.evaluateElementWaitingReady(state);
        }
        case IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT -> {
          this.evaluateElementWaitingForAgentAssignment(state);
        }
        case IN_PROGRESS_EXECUTING -> {
          this.evaluateElementExecuting(state);
        }
        case SUCEEDED -> {

        }
        case FAILED -> {

        }
        case FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT -> {

        }
        case FAILED_TIMED_OUT_EXECUTION -> {

        }
      }
    }
  }

  private void evaluateElementExecuting(
    final ElementState state)
  {
    if (state.element instanceof final NPPlanTaskType task) {
      final var timeoutOpt =
        task.executionTimeout();

      if (timeoutOpt.isPresent()) {
        final var timeout =
          timeoutOpt.get();
        final var timeNow =
          this.clock.instant();
        final var waiting =
          Duration.between(state.timeStartExecute, timeNow);

        if (waiting.compareTo(timeout) > 0) {
          state.status = FAILED_TIMED_OUT_EXECUTION;
          state.timeFinished = timeNow;
          this.stepEvents.add(new TaskExecutionTimedOut(task));
          this.stepEvents.add(new ElementFailed(state.element));
          return;
        }
      }
    }
  }

  private void evaluateElementWaitingForAgentAssignment(
    final ElementState state)
  {
    final var task = (NPPlanTaskType) state.element;

    final var timeoutOpt =
      task.agentAssignmentTimeout();

    if (timeoutOpt.isPresent()) {
      final var timeout =
        timeoutOpt.get();
      final var timeNow =
        this.clock.instant();
      final var waiting =
        Duration.between(state.timeStartWaitAgent, timeNow);

      if (waiting.compareTo(timeout) > 0) {
        state.status = FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT;
        state.timeFinished = timeNow;
        this.stepEvents.add(new TaskAgentAssignmentTimedOut(task));
        this.stepEvents.add(new ElementFailed(state.element));
        return;
      }
    }

    this.publishWantAgentAssignmentEvent(task);
  }

  private void evaluateElementWaitingReady(
    final ElementState state)
  {
    final var element = state.element;
    if (element instanceof final NPPlanTaskType task) {
      state.status = IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT;
      state.timeStartWaitAgent = this.clock.instant();
      this.publishWantAgentAssignmentEvent(task);
      return;
    }

    if (element instanceof NPPlanBarrierType) {
      state.status = SUCEEDED;
      state.timeFinished = this.clock.instant();
      this.stepEvents.add(new ElementSucceeded(element));
      return;
    }
  }

  private void publishWantAgentAssignmentEvent(
    final NPPlanTaskType task)
  {
    final var sameOpt = task.agentMustBeSameAs();
    if (sameOpt.isPresent()) {
      final var same = sameOpt.get();
      final var existingAgent =
        this.elements.get(same.name())
          .agent
          .orElseThrow();

      this.stepEvents.add(new TaskRequiresSpecificAgent(task, existingAgent));
    } else {
      this.stepEvents.add(new TaskRequiresMatchingAgent(task));
    }
  }

  private void evaluateElementWaitingNotReady(
    final ElementState state)
  {
    final var element = state.element;

    final var dependencies =
      element.dependsOn();
    final var dependenciesSucceeded =
      dependencies.stream()
        .map(this.elements::get)
        .allMatch(e -> e.status.isSuccess());

    if (dependenciesSucceeded) {
      state.status = IN_PROGRESS_WAITING_READY;
      state.timeStartReady = this.clock.instant();
      this.stepEvents.add(new ElementBecameReady(element));
    }
  }

  private boolean isSucceeded()
  {
    for (final var terminal : this.terminals) {
      final var name = terminal.name();
      if (!(this.elements.get(name).status.isSuccess())) {
        return false;
      }
    }
    return true;
  }

  private boolean isFailed()
  {
    for (final var element : this.elements.values()) {
      if (element.status.isFailed()) {
        return true;
      }
    }
    return false;
  }
}
