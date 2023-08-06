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

/**
 * The status of a particular plan element.
 */

public enum NPPlanElementStatus
{
  /**
   * The given element is not ready as it is waiting on one or mor dependencies.
   */

  IN_PROGRESS_WAITING_NOT_READY,

  /**
   * The given element is ready to execute.
   */

  IN_PROGRESS_WAITING_READY,

  /**
   * The given element is ready to execute but has not yet been assigned
   * an agent.
   */

  IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT,

  /**
   * The given element is executing now.
   */

  IN_PROGRESS_EXECUTING,

  /**
   * The given element successfully executed.
   */

  SUCEEDED,

  /**
   * The given element failed execution.
   */

  FAILED,

  /**
   * The given element timed out waiting for an agent to be assigned to
   * execute it.
   */

  FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT,

  /**
   * The given element exceeded its execution timeout limit.
   */

  FAILED_TIMED_OUT_EXECUTION;

  /**
   * @return {@code true} if this value denotes an "in progress" state
   */

  public boolean isInProgress()
  {
    return switch (this) {
      case IN_PROGRESS_WAITING_NOT_READY,
        IN_PROGRESS_EXECUTING,
        IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT,
        IN_PROGRESS_WAITING_READY -> true;
      case SUCEEDED,
        FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT,
        FAILED_TIMED_OUT_EXECUTION,
        FAILED -> false;
    };
  }

  /**
   * @return {@code true} if this value denotes a  "successfully completed" state
   */

  public boolean isSuccess()
  {
    return switch (this) {
      case IN_PROGRESS_WAITING_NOT_READY,
        FAILED,
        FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT,
        FAILED_TIMED_OUT_EXECUTION,
        IN_PROGRESS_EXECUTING,
        IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT,
        IN_PROGRESS_WAITING_READY -> false;
      case SUCEEDED -> true;
    };
  }

  /**
   * @return {@code true} if this value denotes a failure state
   */

  public boolean isFailed()
  {
    return switch (this) {
      case IN_PROGRESS_WAITING_NOT_READY,
        SUCEEDED,
        IN_PROGRESS_EXECUTING,
        IN_PROGRESS_WAITING_FOR_AGENT_ASSIGNMENT,
        IN_PROGRESS_WAITING_READY -> false;
      case FAILED,
        FAILED_TIMED_OUT_WAITING_AGENT_ASSIGNMENT,
        FAILED_TIMED_OUT_EXECUTION -> true;
    };
  }
}
