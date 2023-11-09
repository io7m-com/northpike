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

import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.plans.NPPlanElementType;
import com.io7m.northpike.model.plans.NPPlanTaskType;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementBecameReady;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.ElementSucceeded;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskAgentSelectionTimedOut;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskExecutionTimedOut;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresMatchingAgent;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationEventType.TaskRequiresSpecificAgent;

import java.util.Objects;

/**
 * The type of events produced during plan evaluation.
 */

public sealed interface NPPlanEvaluationEventType
  permits ElementBecameReady,
  ElementFailed,
  ElementSucceeded,
  TaskAgentSelectionTimedOut,
  TaskExecutionTimedOut,
  TaskRequiresMatchingAgent,
  TaskRequiresSpecificAgent
{
  /**
   * An element became ready for execution.
   *
   * @param element The element
   */

  record ElementBecameReady(
    NPPlanElementType element)
    implements NPPlanEvaluationEventType
  {
    /**
     * An element became ready for execution.
     */

    public ElementBecameReady
    {
      Objects.requireNonNull(element, "element");
    }

    @Override
    public String toString()
    {
      return "[ElementBecameReady %s]".formatted(this.element.name());
    }
  }

  /**
   * An element successfully executed.
   *
   * @param element The element
   */

  record ElementSucceeded(
    NPPlanElementType element)
    implements NPPlanEvaluationEventType
  {
    /**
     * An element successfully executed.
     */

    public ElementSucceeded
    {
      Objects.requireNonNull(element, "element");
    }

    @Override
    public String toString()
    {
      return "[ElementSucceeded %s]".formatted(this.element.name());
    }
  }

  /**
   * An element failed execution.
   *
   * @param element The element
   */

  record ElementFailed(
    NPPlanElementType element)
    implements NPPlanEvaluationEventType
  {
    /**
     * An element failed execution.
     */

    public ElementFailed
    {
      Objects.requireNonNull(element, "element");
    }

    @Override
    public String toString()
    {
      return "[ElementFailed %s]".formatted(this.element.name());
    }
  }

  /**
   * A task requires an agent to be assigned.
   *
   * @param task The task
   */

  record TaskRequiresMatchingAgent(
    NPPlanTaskType task)
    implements NPPlanEvaluationEventType
  {
    /**
     * A task requires an agent to be assigned.
     */

    public TaskRequiresMatchingAgent
    {
      Objects.requireNonNull(task, "element");
    }

    @Override
    public String toString()
    {
      return "[TaskRequiresMatchingAgent %s]".formatted(this.task.name());
    }
  }

  /**
   * A task requires the specific given agent to be assigned.
   *
   * @param task  The task
   * @param agent The agent
   */

  record TaskRequiresSpecificAgent(
    NPPlanTaskType task,
    NPAgentID agent)
    implements NPPlanEvaluationEventType
  {
    /**
     * A task requires the specific given agent to be assigned.
     */

    public TaskRequiresSpecificAgent
    {
      Objects.requireNonNull(task, "element");
      Objects.requireNonNull(agent, "agent");
    }

    @Override
    public String toString()
    {
      return "[TaskRequiresSpecificAgent %s %s]"
        .formatted(this.task.name(), this.agent.value());
    }
  }

  /**
   * A task timed out waiting for an agent to be selected.
   *
   * @param task The task
   */

  record TaskAgentSelectionTimedOut(
    NPPlanTaskType task)
    implements NPPlanEvaluationEventType
  {
    /**
     * A task timed out waiting for an agent to be selected.
     */

    public TaskAgentSelectionTimedOut
    {
      Objects.requireNonNull(task, "element");
    }

    @Override
    public String toString()
    {
      return "[TaskAgentSelectionTimedOut %s]".formatted(this.task.name());
    }
  }

  /**
   * A task was executing for too long, and timed out.
   *
   * @param task The task
   */

  record TaskExecutionTimedOut(
    NPPlanTaskType task)
    implements NPPlanEvaluationEventType
  {
    /**
     * A task was executing for too long, and timed out.
     */

    public TaskExecutionTimedOut
    {
      Objects.requireNonNull(task, "element");
    }

    @Override
    public String toString()
    {
      return "[TaskExecutionTimedOut %s]".formatted(this.task.name());
    }
  }
}
