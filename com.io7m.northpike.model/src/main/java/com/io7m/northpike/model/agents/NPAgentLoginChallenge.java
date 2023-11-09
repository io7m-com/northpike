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

import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Arrays;
import java.util.Objects;
import java.util.UUID;

/**
 * A login challenge.
 *
 * @param id   The challenge ID
 * @param data The data
 */

public record NPAgentLoginChallenge(
  UUID id,
  byte[] data)
{
  /**
   * A login challenge.
   *
   * @param id   The challenge ID
   * @param data The data
   */

  public NPAgentLoginChallenge
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(data, "data");
    data = data.clone();
  }

  /**
   * Generate a new login challenge.
   *
   * @return The login challenge
   */

  public static NPAgentLoginChallenge generate()
  {
    try {
      final var data =
        new byte[64];
      final var rng =
        SecureRandom.getInstanceStrong();

      rng.nextBytes(data);
      return new NPAgentLoginChallenge(UUID.randomUUID(), data);
    } catch (final NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  public boolean equals(final Object o)
  {
    if (this == o) {
      return true;
    }
    if (o == null || !this.getClass().equals(o.getClass())) {
      return false;
    }
    final NPAgentLoginChallenge that = (NPAgentLoginChallenge) o;
    return Objects.equals(this.id, that.id)
           && Arrays.equals(this.data, that.data);
  }

  @Override
  public int hashCode()
  {
    int result = Objects.hash(this.id);
    result = 31 * result + Arrays.hashCode(this.data);
    return result;
  }
}
