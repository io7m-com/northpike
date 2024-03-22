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


package com.io7m.northpike.protocol.agent;

import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPWorkItemIdentifier;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

/**
 * A work item produced a line of output.
 *
 * @param messageID  The ID of this message
 * @param timestamp  The time the output was produced
 * @param eventIndex The index of the log output line
 * @param eventType The event type
 * @param identifier The work item identifier
 * @param attributes The message attributes
 * @param message    The line of output
 * @param exception  The exception, if any
 */

public record NPACommandCWorkItemOutput(
  UUID messageID,
  OffsetDateTime timestamp,
  long eventIndex,
  String eventType,
  NPWorkItemIdentifier identifier,
  Map<String, String> attributes,
  String message,
  Optional<NPStoredException> exception)
  implements NPACommandC2SType<NPAResponseOK>
{
  /**
   * A work item produced a line of output.
   *
   * @param messageID  The ID of this message
   * @param timestamp  The time the output was produced
   * @param eventIndex The index of the log output line
   * @param eventType The event type
   * @param identifier The work item identifier
   * @param attributes The message attributes
   * @param message    The line of output
   * @param exception  The exception, if any
   */

  public NPACommandCWorkItemOutput
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(identifier, "identifier");
    Objects.requireNonNull(eventType, "eventType");
    Objects.requireNonNull(attributes, "attributes");
    Objects.requireNonNull(message, "message");
    Objects.requireNonNull(exception, "exception");
  }

  @Override
  public Class<NPAResponseOK> responseClass()
  {
    return NPAResponseOK.class;
  }
}
