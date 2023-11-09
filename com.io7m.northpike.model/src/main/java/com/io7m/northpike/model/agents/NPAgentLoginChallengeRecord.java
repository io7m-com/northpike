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


package com.io7m.northpike.model.agents;

import java.time.OffsetDateTime;
import java.util.Objects;
import java.util.UUID;

/**
 * A login challenge record.
 *
 * @param timeCreated   The time the challenge was created
 * @param sourceAddress The address that created the challenge
 * @param key           The key
 * @param challenge     The challenge
 */

public record NPAgentLoginChallengeRecord(
  OffsetDateTime timeCreated,
  String sourceAddress,
  NPAgentKeyPublicType key,
  NPAgentLoginChallenge challenge)
{
  /**
   * A login challenge.
   *
   * @param timeCreated   The time the challenge was created
   * @param sourceAddress The address that created the challenge
   * @param key           The key
   * @param challenge     The challenge
   */

  public NPAgentLoginChallengeRecord
  {
    Objects.requireNonNull(timeCreated, "timeCreated");
    Objects.requireNonNull(sourceAddress, "sourceAddress");
    Objects.requireNonNull(key, "key");
    Objects.requireNonNull(challenge, "challenge");
  }

  /**
   * @return The unique challenge ID
   */

  public UUID id()
  {
    return this.challenge.id();
  }
}
