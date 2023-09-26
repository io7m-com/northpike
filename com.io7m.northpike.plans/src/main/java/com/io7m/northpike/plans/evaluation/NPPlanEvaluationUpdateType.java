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
import com.io7m.northpike.model.plans.NPPlanElementName;

import java.util.Objects;

/**
 * An update handed to the evaluation of a plan to notify the plan that
 * some external event occurred.
 */

public sealed interface NPPlanEvaluationUpdateType
{
  /**
   * The given agent accepted the given task for execution.
   *
   * @param task  The task
   * @param agent The agent
   */

  record AgentAcceptedTask(
    NPPlanElementName task,
    NPAgentID agent)
    implements NPPlanEvaluationUpdateType
  {
    /**
     * The given agent accepted the given task for execution.
     */

    public AgentAcceptedTask
    {
      Objects.requireNonNull(task, "task");
      Objects.requireNonNull(agent, "agent");
    }
  }

  /**
   * The given agent reported that the given task successfully completed
   * execution.
   *
   * @param task  The task
   * @param agent The agent
   */

  record AgentReportedTaskSuccess(
    NPPlanElementName task,
    NPAgentID agent)
    implements NPPlanEvaluationUpdateType
  {
    /**
     * The given agent reported that the given task successfully completed
     * execution.
     */

    public AgentReportedTaskSuccess
    {
      Objects.requireNonNull(task, "task");
      Objects.requireNonNull(agent, "agent");
    }
  }

  /**
   * The given agent reported that the given task failed.
   *
   * @param task  The task
   * @param agent The agent
   */

  record AgentReportedTaskFailure(
    NPPlanElementName task,
    NPAgentID agent)
    implements NPPlanEvaluationUpdateType
  {
    /**
     * The given agent reported that the given task failed.
     */

    public AgentReportedTaskFailure
    {
      Objects.requireNonNull(task, "task");
      Objects.requireNonNull(agent, "agent");
    }
  }
}
