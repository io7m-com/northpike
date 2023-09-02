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

import com.io7m.lanark.core.RDottedName;

import java.util.Objects;

/**
 * The type of tool names.
 *
 * @param value The value
 */

public record NPToolName(
  RDottedName value)
  implements Comparable<NPToolName>
{
  /**
   * The type of tool names.
   *
   * @param value The value
   */

  public NPToolName
  {
    Objects.requireNonNull(value, "value");
  }

  @Override
  public String toString()
  {
    return this.value.value();
  }

  @Override
  public int compareTo(
    final NPToolName other)
  {
    return this.value.compareTo(other.value);
  }

  /**
   * Parse a tool name.
   *
   * @param name The raw name
   *
   * @return A tool name
   */

  public static NPToolName of(
    final String name)
  {
    return new NPToolName(new RDottedName(name));
  }
}
