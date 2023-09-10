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
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.northpike.plans.NPPlanBarrierDescription;
import com.io7m.northpike.plans.NPPlanElementDescriptionType;
import com.io7m.northpike.plans.NPPlanElementName;
import org.xml.sax.Attributes;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * A barrier parser.
 */

public final class NPP1Barrier
  implements BTElementHandlerType<Object, NPPlanElementDescriptionType>
{
  private NPPlanElementName name;
  private String description;

  private Set<NPPlanElementName> dependsOn =
    new TreeSet<>();

  /**
   * A barrier parser.
   *
   * @param context The parse context
   */

  public NPP1Barrier(
    final BTElementParsingContextType context)
  {

  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        element("DependsOn"),
        Blackthorne.forScalarAttribute(
          element("DependsOn"),
          (c, a) -> new NPP1DependsOn(NPPlanElementName.of(a.getValue("Task")))
        )
      )
    );
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.name =
      NPPlanElementName.of(attributes.getValue("Name"));
    this.description =
      attributes.getValue("Description");
  }

  @Override
  public NPPlanElementDescriptionType onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPPlanBarrierDescription(
      this.name,
      this.description,
      this.dependsOn
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    if (result instanceof final NPP1DependsOn e) {
      this.dependsOn.add(e.task());
      return;
    }

    throw new IllegalStateException(
      "Unrecognized result: %s".formatted(result)
    );
  }
}
