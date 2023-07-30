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


package com.io7m.northpike.model;

import java.time.OffsetDateTime;
import java.util.Objects;

/**
 * An inclusive range of time values.
 *
 * @param lower The lower bound
 * @param upper The upper bound
 */

public record NPTimeRange(
  OffsetDateTime lower,
  OffsetDateTime upper)
{
  private static final OffsetDateTime TIME_LOWEST =
    OffsetDateTime.parse("1970-01-01T00:00:00+00:00");

  private static final NPTimeRange LARGEST =
    new NPTimeRange(
      TIME_LOWEST,
      TIME_LOWEST.plusYears(10_000L)
    );

  /**
   * An inclusive range of time values.
   *
   * @param lower The lower bound
   * @param upper The upper bound
   */

  public NPTimeRange
  {
    Objects.requireNonNull(lower, "lower");
    Objects.requireNonNull(upper, "upper");

    if (lower.isAfter(upper)) {
      throw new NPValidityException("Upper time must be <= lower time.");
    }
  }

  /**
   * @return The largest possible time range
   */

  public static NPTimeRange largest()
  {
    return LARGEST;
  }
}
