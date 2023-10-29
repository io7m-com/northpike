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


package com.io7m.northpike.model;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * A log record produced when executing a work item.
 *
 * @param workItem   The work item
 * @param timestamp  The timestamp
 * @param attributes The attributes
 * @param message    The message
 * @param exception  The associated exception, if any
 */

public record NPWorkItemLogRecord(
  NPWorkItemIdentifier workItem,
  OffsetDateTime timestamp,
  Map<String, String> attributes,
  String message,
  Optional<NPStoredException> exception)
{
  /**
   * A log record produced when executing a work item.
   *
   * @param workItem   The work item
   * @param timestamp  The timestamp
   * @param attributes The attributes
   * @param message    The message
   * @param exception  The associated exception, if any
   */

  public NPWorkItemLogRecord
  {
    Objects.requireNonNull(workItem, "workItem");
    Objects.requireNonNull(timestamp, "timestamp");
    Objects.requireNonNull(attributes, "attributes");
    Objects.requireNonNull(message, "message");
    Objects.requireNonNull(exception, "exception");
  }
}
