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


package com.io7m.northpike.plans;

import java.time.Duration;
import java.util.Objects;

/**
 * The default timeouts for plan evaluation.
 *
 * @param agentSelection The maximum time that can elapse waiting for agent selection for a task
 * @param taskExecution  The maximum time that can elapse when a single task is execution
 */

public record NPPlanTimeouts(
  Duration agentSelection,
  Duration taskExecution)
{
  private static final NPPlanTimeouts DEFAULT_TIMEOUTS =
    new NPPlanTimeouts(
      Duration.ofSeconds(31556926L),
      Duration.ofSeconds(31556926L)
    );

  /**
   * The default timeouts for plan evaluation.
   *
   * @param agentSelection The maximum time that can elapse waiting for agent selection for a task
   * @param taskExecution  The maximum time that can elapse when a single task is execution
   */

  public NPPlanTimeouts
  {
    Objects.requireNonNull(agentSelection, "agentSelection");
    Objects.requireNonNull(taskExecution, "taskExecution");
  }

  /**
   * @return The default timeout values
   */

  public static NPPlanTimeouts defaultTimeouts()
  {
    return DEFAULT_TIMEOUTS;
  }
}
