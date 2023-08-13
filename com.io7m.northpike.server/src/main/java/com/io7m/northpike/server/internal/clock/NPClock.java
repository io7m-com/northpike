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


package com.io7m.northpike.server.internal.clock;

import java.time.Clock;
import java.util.Objects;

/**
 * A clock service.
 */

public final class NPClock implements NPClockServiceType
{
  private final Clock clock;

  /**
   * A clock service.
   *
   * @param inClock The underlying clock
   */

  public NPClock(
    final Clock inClock)
  {
    this.clock = Objects.requireNonNull(inClock, "clock");
  }

  @Override
  public Clock clock()
  {
    return this.clock;
  }

  @Override
  public String description()
  {
    return "Clock service.";
  }

  @Override
  public String toString()
  {
    return "[NPClock 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
