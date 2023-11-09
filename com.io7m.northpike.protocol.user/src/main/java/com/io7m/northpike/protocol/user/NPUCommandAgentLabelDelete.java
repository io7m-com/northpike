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


package com.io7m.northpike.protocol.user;

import com.io7m.northpike.model.agents.NPAgentLabelName;

import java.util.Objects;
import java.util.Set;
import java.util.UUID;

/**
 * Delete labels.
 *
 * @param messageID The message ID
 * @param labels    The labels
 */

public record NPUCommandAgentLabelDelete(
  UUID messageID,
  Set<NPAgentLabelName> labels)
  implements NPUCommandType<NPUResponseOK>
{
  /**
   * Delete labels.
   *
   * @param messageID The message ID
   * @param labels    The labels
   */

  public NPUCommandAgentLabelDelete
  {
    Objects.requireNonNull(messageID, "messageId");
    Objects.requireNonNull(labels, "labels");
  }

  @Override
  public Class<NPUResponseOK> responseClass()
  {
    return NPUResponseOK.class;
  }
}
