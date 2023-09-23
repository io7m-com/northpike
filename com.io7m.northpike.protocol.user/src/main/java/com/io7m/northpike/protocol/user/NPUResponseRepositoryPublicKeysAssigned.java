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

import com.io7m.northpike.model.NPFingerprint;

import java.util.Objects;
import java.util.Set;
import java.util.UUID;

/**
 * The set of keys assigned to a repository.
 *
 * @param messageID     The message ID
 * @param correlationID The command that prompted this response
 * @param keys          The keys
 */

public record NPUResponseRepositoryPublicKeysAssigned(
  UUID messageID,
  UUID correlationID,
  Set<NPFingerprint> keys)
  implements NPUResponseType
{
  /**
   * The set of keys assigned to a repository.
   *
   * @param messageID     The message ID
   * @param correlationID The command that prompted this response
   * @param keys          The keys
   */

  public NPUResponseRepositoryPublicKeysAssigned
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(correlationID, "correlationID");
    Objects.requireNonNull(keys, "keys");
  }

  /**
   * Create a response with a random message ID, with a correlation
   * ID matched to the given command.
   *
   * @param command The command
   * @param keys    The keys
   *
   * @return An OK response
   */

  public static NPUResponseRepositoryPublicKeysAssigned createCorrelated(
    final NPUCommandType<?> command,
    final Set<NPFingerprint> keys)
  {
    return new NPUResponseRepositoryPublicKeysAssigned(
      UUID.randomUUID(),
      command.messageID(),
      keys
    );
  }
}
