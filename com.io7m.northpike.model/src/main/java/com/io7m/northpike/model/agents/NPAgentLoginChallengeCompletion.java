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

import java.util.Objects;
import java.util.UUID;

/**
 * A login challenge completion.
 *
 * @param id        The challenge ID
 * @param signature The signature
 */

public record NPAgentLoginChallengeCompletion(
  UUID id,
  byte[] signature)
{
  /**
   * A login challenge completion.
   *
   * @param id        The challenge ID
   * @param signature The signature
   */

  public NPAgentLoginChallengeCompletion
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(signature, "signature");
    signature = signature.clone();
  }
}
