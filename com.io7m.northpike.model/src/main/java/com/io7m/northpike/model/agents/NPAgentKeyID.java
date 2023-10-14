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

import com.io7m.northpike.model.NPValidityException;

import java.util.Objects;
import java.util.regex.Pattern;

/**
 * An agent key ID.
 *
 * @param value The ID value
 */

public record NPAgentKeyID(String value)
{
  private static final Pattern VALID_VALUE =
    Pattern.compile("[a-f0-9]{32,}");

  /**
   * An agent ID.
   *
   * @param value The ID value
   */

  public NPAgentKeyID
  {
    Objects.requireNonNull(value, "value");

    if (!VALID_VALUE.matcher(value).matches()) {
      throw new NPValidityException(
        "Key ID must match the pattern %s".formatted(VALID_VALUE)
      );
    }
  }

  @Override
  public String toString()
  {
    return this.value.toString();
  }
}
