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


package com.io7m.northpike.server.internal.schedule;

import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.telemetry.api.NPEventSeverity;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;

/**
 * An assignment was scheduled to run at a future time.
 *
 * @param assignment The assignment
 * @param time       The time
 */

public record NPSchedulerScheduled(
  NPAssignmentName assignment,
  OffsetDateTime time)
  implements NPSchedulerEventType
{
  /**
   * An assignment was scheduled to run at a future time.
   *
   * @param assignment The assignment
   * @param time       The time
   */

  public NPSchedulerScheduled
  {
    Objects.requireNonNull(assignment, "assignment");
    Objects.requireNonNull(time, "time");
  }

  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.INFO;
  }

  @Override
  public String name()
  {
    return "AssignmentScheduled";
  }

  @Override
  public String message()
  {
    return "Scheduled";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("Assignment", this.assignment.toString()),
      Map.entry("TargetTime", this.time.toString())
    );
  }
}
