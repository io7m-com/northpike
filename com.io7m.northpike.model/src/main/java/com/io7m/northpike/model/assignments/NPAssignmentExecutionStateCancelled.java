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


package com.io7m.northpike.model.assignments;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;

import static java.util.Map.entry;

/**
 * An execution was cancelled.
 *
 * @param id          The execution ID
 * @param timeCreated The time created
 * @param timeStarted The time started
 * @param timeEnded   The time ended/cancelled
 * @param request     The request
 */

public record NPAssignmentExecutionStateCancelled(
  NPAssignmentExecutionID id,
  NPAssignmentExecutionRequest request,
  OffsetDateTime timeCreated,
  OffsetDateTime timeStarted,
  OffsetDateTime timeEnded)
  implements NPAssignmentExecutionStateType
{
  /**
   * An execution was cancelled.
   *
   * @param id          The execution ID
   * @param timeCreated The time created
   *                    @param timeStarted The time started
   * @param timeEnded   The time ended/cancelled
   * @param request     The request
   */

  public NPAssignmentExecutionStateCancelled
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(request, "request");
    Objects.requireNonNull(timeCreated, "timeCreated");
    Objects.requireNonNull(timeStarted, "timeStarted");
    Objects.requireNonNull(timeEnded, "timeEnded");
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      entry("Assignment", this.request.assignment().toString()),
      entry("AssignmentExecutionID", this.id.toString()),
      entry("CommitID", this.request.commit().toString()),
      entry("Status", this.stateName()),
      entry("TimeCreated", this.timeCreated.toString()),
      entry("TimeEnded", this.timeEnded.toString()),
      entry("TimeStarted", this.timeStarted.toString())
    );
  }

  @Override
  public NPAssignmentExecutionStateKind state()
  {
    return NPAssignmentExecutionStateKind.CANCELLED;
  }
}
