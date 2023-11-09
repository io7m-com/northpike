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
import com.io7m.blackthorne.core.BTQualifiedName;
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;

import java.util.Map;

import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * Functions over set comparisons.
 */

public final class NPP1SetComparisons
{
  private NPP1SetComparisons()
  {

  }

  /**
   * @return Set comparison parsers
   */

  public static Map<BTQualifiedName,
    BTElementHandlerConstructorType<
      ?, ? extends NPComparisonSetType<NPAgentLabelName>>> expressions()
  {
    return Map.ofEntries(
      Map.entry(element("SetIsAnything"), setIsAnything()),
      Map.entry(element("SetIsSupersetOf"), setIsSupersetOf()),
      Map.entry(element("SetIsSubsetOf"), setIsSubsetOf()),
      Map.entry(element("SetIsEqualTo"), setIsEqualTo()),
      Map.entry(element("SetIsNotEqualTo"), setIsNotEqualTo()),
      Map.entry(element("SetIsOverlapping"), setIsOverlapping())
    );
  }

  /**
   * @return Set comparison parser
   */

  public static BTElementHandlerConstructorType<
    ?, NPComparisonSetType<NPAgentLabelName>> setIsAnything()
  {
    return Blackthorne.forScalarAttribute(
      element("SetIsAnything"),
      (context, attributes) -> new NPComparisonSetType.Anything<>()
    );
  }

  /**
   * @return Set comparison parser
   */

  public static BTElementHandlerConstructorType<
    ?, NPComparisonSetType<NPAgentLabelName>> setIsSupersetOf()
  {
    return NPP1SetIsSupersetOf::new;
  }

  /**
   * @return Set comparison parser
   */

  public static BTElementHandlerConstructorType<
    ?, NPComparisonSetType<NPAgentLabelName>> setIsSubsetOf()
  {
    return NPP1SetIsSubsetOf::new;
  }

  /**
   * @return Set comparison parser
   */

  public static BTElementHandlerConstructorType<
    ?, NPComparisonSetType<NPAgentLabelName>> setIsOverlapping()
  {
    return NPP1SetIsOverlapping::new;
  }

  /**
   * @return Set comparison parser
   */

  public static BTElementHandlerConstructorType<
    ?, NPComparisonSetType<NPAgentLabelName>> setIsEqualTo()
  {
    return NPP1SetIsEqualTo::new;
  }

  /**
   * @return Set comparison parser
   */

  public static BTElementHandlerConstructorType<
    ?, NPComparisonSetType<NPAgentLabelName>> setIsNotEqualTo()
  {
    return NPP1SetIsNotEqualTo::new;
  }

  /**
   * @return Set element parser
   */

  public static BTElementHandlerConstructorType<?, NPAgentLabelName> setElement()
  {
    return Blackthorne.forScalarAttribute(
      element("SetElement"),
      (context, attributes) -> {
        return NPAgentLabelName.of(attributes.getValue("Value"));
      }
    );
  }
}
