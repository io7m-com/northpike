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


package com.io7m.northpike.shell.commons;


import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.agents.NPAgentLabelSet;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @see NPAgentLabelSet
 */

public final class NPAgentLabelSetConverter
  implements QValueConverterType<NPAgentLabelSet>
{
  /**
   * @see NPAgentLabelSet
   */

  public NPAgentLabelSetConverter()
  {

  }

  @Override
  public NPAgentLabelSet convertFromString(
    final String text)
  {
    if (text.trim().isEmpty()) {
      return new NPAgentLabelSet(Set.of());
    }

    return new NPAgentLabelSet(
      Arrays.stream(text.split(","))
        .map(NPAgentLabelName::of)
        .collect(Collectors.toUnmodifiableSet())
    );
  }

  @Override
  public String convertToString(
    final NPAgentLabelSet value)
  {
    return value.labels()
      .stream()
      .map(NPAgentLabelName::toString)
      .collect(Collectors.joining(","));
  }

  @Override
  public NPAgentLabelSet exampleValue()
  {
    return new NPAgentLabelSet(
      Set.of(
        NPAgentLabelName.of("label0"),
        NPAgentLabelName.of("label1"),
        NPAgentLabelName.of("label2")
      )
    );
  }

  @Override
  public String syntax()
  {
    return "<label-name> [',' <label-name>]";
  }

  @Override
  public Class<NPAgentLabelSet> convertedClass()
  {
    return NPAgentLabelSet.class;
  }
}
