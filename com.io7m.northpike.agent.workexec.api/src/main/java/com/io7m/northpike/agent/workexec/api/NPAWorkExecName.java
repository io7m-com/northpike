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


package com.io7m.northpike.agent.workexec.api;

import com.io7m.lanark.core.RDottedName;

import java.util.Comparator;
import java.util.Objects;

/**
 * The type of work executor names.
 *
 * @param value The name value
 */

public record NPAWorkExecName(RDottedName value)
  implements Comparable<NPAWorkExecName>
{
  /**
   * The type of work executor names.
   *
   * @param value The name value
   */

  public NPAWorkExecName
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
    final NPAWorkExecName other)
  {
    return Comparator.comparing(NPAWorkExecName::value)
      .compare(this, other);
  }

  /**
   * Construct a work executor name.
   *
   * @param value The name value
   *
   * @return A work executor name
   */

  public static NPAWorkExecName of(
    final String value)
  {
    return new NPAWorkExecName(new RDottedName(value));
  }
}
