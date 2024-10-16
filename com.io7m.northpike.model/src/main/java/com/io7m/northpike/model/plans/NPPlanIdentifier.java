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


package com.io7m.northpike.model.plans;

import java.util.Objects;

/**
 * The unique identifier for a plan.
 *
 * @param name    The plan name
 * @param version The plan version
 */

public record NPPlanIdentifier(
  NPPlanName name,
  long version)
{
  /**
   * The unique identifier for a plan.
   *
   * @param name    The plan name
   * @param version The plan version
   */

  public NPPlanIdentifier
  {
    Objects.requireNonNull(name, "name");
  }

  @Override
  public String toString()
  {
    return "%s:%s".formatted(
      this.name.toString(),
      Long.toUnsignedString(this.version)
    );
  }

  /**
   * Parse an identifier.
   *
   * @param name    The name string
   * @param version The version
   *
   * @return An identifier
   */

  public static NPPlanIdentifier of(
    final String name,
    final long version)
  {
    return new NPPlanIdentifier(
      NPPlanName.of(name),
      version
    );
  }
}
