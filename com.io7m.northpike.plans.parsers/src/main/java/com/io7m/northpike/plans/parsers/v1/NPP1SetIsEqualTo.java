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


package com.io7m.northpike.plans.parsers.v1;

import com.io7m.blackthorne.core.BTElementHandlerConstructorType;
import com.io7m.blackthorne.core.BTElementHandlerType;
import com.io7m.blackthorne.core.BTElementParsingContextType;
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static com.io7m.northpike.plans.parsers.v1.NPP1.element;
import static com.io7m.northpike.plans.parsers.v1.NPP1SetComparisons.setElement;

/**
 * SetIsEqualTo
 */

public final class NPP1SetIsEqualTo
  implements BTElementHandlerType<NPAgentLabelName, NPComparisonSetType<NPAgentLabelName>>
{
  private final HashSet<NPAgentLabelName> elements;

  /**
   * SetIsEqualTo
   *
   * @param context The parse context
   */

  public NPP1SetIsEqualTo(
    final BTElementParsingContextType context)
  {
    this.elements = new HashSet<>();
  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPAgentLabelName>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.of(element("SetElement"), setElement());
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPAgentLabelName result)
  {
    this.elements.add(result);
  }

  @Override
  public NPComparisonSetType<NPAgentLabelName> onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPComparisonSetType.IsEqualTo<>(Set.copyOf(this.elements));
  }
}
