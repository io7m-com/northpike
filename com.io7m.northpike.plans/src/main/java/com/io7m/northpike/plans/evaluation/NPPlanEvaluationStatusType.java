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

import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusFailed;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusInProgress;
import com.io7m.northpike.plans.evaluation.NPPlanEvaluationStatusType.StatusSucceeded;

import java.util.List;
import java.util.Objects;

/**
 * The evaluation status of a plan.
 */

public sealed interface NPPlanEvaluationStatusType
  permits StatusFailed,
  StatusInProgress,
  StatusSucceeded
{
  /**
   * @return The events produced by the most recent step of evaluation
   */

  List<NPPlanEvaluationEventType> events();

  /**
   * @return {@code true} if this status is a terminal status
   */

  boolean isTerminal();

  /**
   * The plan failed.
   *
   * @param events The events produced by the most recent step of evaluation
   */

  record StatusFailed(
    List<NPPlanEvaluationEventType> events)
    implements NPPlanEvaluationStatusType
  {
    /**
     * The plan failed.
     */

    public StatusFailed
    {
      Objects.requireNonNull(events, "events");
    }

    @Override
    public boolean isTerminal()
    {
      return true;
    }
  }

  /**
   * The plan is still in progress.
   *
   * @param events The events produced by the most recent step of evaluation
   */

  record StatusInProgress(
    List<NPPlanEvaluationEventType> events)
    implements NPPlanEvaluationStatusType
  {
    /**
     * The plan is still in progress.
     */

    public StatusInProgress
    {
      Objects.requireNonNull(events, "events");
    }

    @Override
    public boolean isTerminal()
    {
      return false;
    }
  }

  /**
   * The plan succeeded.
   *
   * @param events The events produced by the most recent step of evaluation
   */

  record StatusSucceeded(
    List<NPPlanEvaluationEventType> events)
    implements NPPlanEvaluationStatusType
  {
    /**
     * The plan succeeded.
     */

    public StatusSucceeded
    {
      Objects.requireNonNull(events, "events");
    }

    @Override
    public boolean isTerminal()
    {
      return true;
    }
  }
}
