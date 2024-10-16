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
 * An assignment execution could not be created.
 *
 * @param id          The execution ID
 * @param timeCreated The time of the creation attempt
 * @param request     The request
 */

public record NPAssignmentExecutionStateCreationFailed(
  NPAssignmentExecutionID id,
  NPAssignmentExecutionRequest request,
  OffsetDateTime timeCreated)
  implements NPAssignmentExecutionStateType
{
  /**
   * An assignment execution could not be created.
   *
   * @param id          The execution ID
   * @param timeCreated The time of the creation attempt
   * @param request     The request
   */

  public NPAssignmentExecutionStateCreationFailed
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(request, "request");
    Objects.requireNonNull(timeCreated, "timeCreated");
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      entry("Assignment", this.request.assignment().toString()),
      entry("CommitID", this.request.commit().toString()),
      entry("Status", this.stateName()),
      entry("TimeCreated", this.timeCreated.toString())
    );
  }

  @Override
  public NPAssignmentExecutionStateKind state()
  {
    return NPAssignmentExecutionStateKind.CREATION_FAILED;
  }
}
