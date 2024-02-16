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

import com.io7m.northpike.model.NPDocumentation;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.telemetry.api.NPEventSeverity;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;

/**
 * An assignment has been asked to execute now.
 *
 * @param assignment   The assignment
 * @param commitsSince Build commits created later than this time
 */

@NPDocumentation("An assignment has been asked to execute now.")
public record NPSchedulerExecute(
  NPAssignmentName assignment,
  OffsetDateTime commitsSince)
  implements NPSchedulerEventType
{
  /**
   * An assignment has been asked to execute now.
   *
   * @param assignment   The assignment
   * @param commitsSince Build commits created later than this time
   */

  public NPSchedulerExecute
  {
    Objects.requireNonNull(assignment, "assignment");
    Objects.requireNonNull(commitsSince, "commitsSince");
  }

  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.INFO;
  }

  @Override
  public String name()
  {
    return "AssignmentExecute";
  }

  @Override
  public String message()
  {
    return "Execute";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("Assignment", this.assignment.toString()),
      Map.entry("CommitsSince", this.commitsSince.toString())
    );
  }
}
