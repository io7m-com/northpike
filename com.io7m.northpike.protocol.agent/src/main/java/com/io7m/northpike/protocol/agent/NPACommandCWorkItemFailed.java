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

import com.io7m.northpike.model.NPWorkItemIdentifier;

import java.util.Objects;
import java.util.UUID;

/**
 * A work item finished executing with a failure.
 *
 * @param messageID  The ID of this message
 * @param identifier The identifier
 */

public record NPACommandCWorkItemFailed(
  UUID messageID,
  NPWorkItemIdentifier identifier)
  implements NPACommandC2SType<NPAResponseOK>
{
  /**
   * A work item finished executing with a failure.
   *
   * @param messageID  The ID of this message
   * @param identifier The identifier
   */

  public NPACommandCWorkItemFailed
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(identifier, "identifier");
  }

  @Override
  public Class<NPAResponseOK> responseClass()
  {
    return NPAResponseOK.class;
  }
}
