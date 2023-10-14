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

import com.io7m.lanark.core.RDottedName;

import java.util.Comparator;
import java.util.Objects;

/**
 * The type of local agent names.
 *
 * @param value The name value
 */

public record NPAgentLocalName(RDottedName value)
  implements Comparable<NPAgentLocalName>
{
  /**
   * The type of local agent names.
   *
   * @param value The name value
   */

  public NPAgentLocalName
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
    final NPAgentLocalName other)
  {
    return Comparator.comparing(NPAgentLocalName::value)
      .compare(this, other);
  }

  /**
   * Construct a local agent name.
   *
   * @param value The name value
   *
   * @return An agent name
   */

  public static NPAgentLocalName of(
    final String value)
  {
    return new NPAgentLocalName(new RDottedName(value));
  }
}
