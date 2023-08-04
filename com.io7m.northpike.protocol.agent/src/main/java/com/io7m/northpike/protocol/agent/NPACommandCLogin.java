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

import com.io7m.northpike.model.NPKey;

import java.util.Objects;
import java.util.UUID;

/**
 * Log in.
 *
 * @param messageID The ID of this message
 * @param key       The agent key
 */

public record NPACommandCLogin(
  UUID messageID,
  NPKey key)
  implements NPACommandC2SType<NPAResponseOK>
{
  /**
   * Log in.
   *
   * @param messageID The ID of this message
   * @param key       The agent key
   */

  public NPACommandCLogin
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(key, "key");
  }

  /**
   * Create a new message with a generated message ID.
   *
   * @param key The key
   *
   * @return The message
   */

  public static NPACommandCLogin of(
    final NPKey key)
  {
    return new NPACommandCLogin(UUID.randomUUID(), key);
  }

  @Override
  public Class<NPAResponseOK> responseClass()
  {
    return NPAResponseOK.class;
  }
}
