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

import java.util.Comparator;
import java.util.Objects;

/**
 * The unique identifier of a tool execution description.
 *
 * @param name    The name of the execution description
 * @param version The version of execution description
 */

public record NPToolExecutionIdentifier(
  NPToolExecutionName name,
  long version)
  implements Comparable<NPToolExecutionIdentifier>
{
  /**
   * The unique identifier of a tool execution description.
   *
   * @param name    The name of the execution description
   * @param version The version of execution description
   */

  public NPToolExecutionIdentifier
  {
    Objects.requireNonNull(name, "name");
  }

  /**
   * @param name    The name of the execution description
   * @param version The version of execution description
   *
   * @return A unique identifier of a tool execution description.
   */

  public static NPToolExecutionIdentifier of(
    final String name,
    final long version)
  {
    return new NPToolExecutionIdentifier(NPToolExecutionName.of(name), version);
  }

  @Override
  public int compareTo(
    final NPToolExecutionIdentifier other)
  {
    return Comparator.comparing(NPToolExecutionIdentifier::name)
      .thenComparingLong(NPToolExecutionIdentifier::version)
      .compare(this, other);
  }
}
