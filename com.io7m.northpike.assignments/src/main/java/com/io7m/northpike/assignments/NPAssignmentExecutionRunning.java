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


package com.io7m.northpike.assignments;

import java.time.OffsetDateTime;
import java.util.Objects;

/**
 * An assignment was started.
 *
 * @param timeCreated The time the execution was created
 * @param timeStarted The time the execution was started
 */

public record NPAssignmentExecutionRunning(
  OffsetDateTime timeCreated,
  OffsetDateTime timeStarted)
  implements NPAssignmentExecutionStatusType
{
  /**
   * An assignment was started.
   *
   * @param timeCreated The time the execution was created
   * @param timeStarted The time the execution was started
   */

  public NPAssignmentExecutionRunning
  {
    Objects.requireNonNull(timeCreated, "timeCreated");
    Objects.requireNonNull(timeStarted, "timeStarted");
  }

  @Override
  public NPAssignmentExecutionFailed fail(
    final OffsetDateTime time)
  {
    return new NPAssignmentExecutionFailed(
      this.timeCreated,
      this.timeStarted,
      time
    );
  }

  @Override
  public String name()
  {
    return "Running";
  }

  @Override
  public NPAssignmentExecutionSucceeded succeed(
    final OffsetDateTime time)
  {
    return new NPAssignmentExecutionSucceeded(
      this.timeCreated,
      this.timeStarted,
      time
    );
  }
}
