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

/**
 * An assignment execution log message.
 *
 * @param executionId The execution ID
 * @param time        The message time
 * @param type        The message type
 * @param message     The message
 * @param attributes  The attributes
 */

public record NPAssignmentExecutionLogMessage(
  NPAssignmentExecutionID executionId,
  OffsetDateTime time,
  String type,
  String message,
  Map<String, String> attributes)
{
  /**
   * An assignment execution log message.
   *
   * @param executionId The execution ID
   * @param time        The message time
   * @param type        The message type
   * @param message     The message
   * @param attributes  The attributes
   */

  public NPAssignmentExecutionLogMessage
  {
    Objects.requireNonNull(executionId, "executionId");
    Objects.requireNonNull(time, "time");
    Objects.requireNonNull(type, "type");
    Objects.requireNonNull(message, "message");
    Objects.requireNonNull(attributes, "attributes");
  }
}
