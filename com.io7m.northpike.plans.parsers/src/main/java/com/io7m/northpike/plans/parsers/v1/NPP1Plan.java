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
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.plans.NPPlanElementName;
import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanTimeouts;
import com.io7m.northpike.plans.parsers.NPPlanDescription;
import com.io7m.northpike.plans.parsers.NPPlanElementDescriptionType;
import org.xml.sax.Attributes;

import java.util.HashMap;
import java.util.Map;

import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * A plan parser.
 */

public final class NPP1Plan
  implements BTElementHandlerType<Object, NPPlanDescription>
{
  private NPPlanIdentifier identifier;
  private Map<NPToolReferenceName, NPToolReference> toolReferences;
  private Map<NPPlanElementName, NPPlanElementDescriptionType> elements;
  private NPPlanTimeouts timeouts;

  /**
   * A plan parser.
   *
   * @param context The parse context
   */

  public NPP1Plan(
    final BTElementParsingContextType context)
  {
    this.toolReferences = new HashMap<>();
    this.elements = new HashMap<>();
    this.timeouts = NPPlanTimeouts.defaultTimeouts();
  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ?>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        element("Task"),
        NPP1Handlers.task()
      ),
      Map.entry(
        element("Barrier"),
        NPP1Handlers.barrier()
      ),
      Map.entry(
        element("Tools"),
        NPP1Handlers.tools()
      ),
      Map.entry(
        element("Timeouts"),
        NPP1Timeouts::new
      )
    );
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.identifier =
      NPPlanIdentifier.of(
        attributes.getValue("Name"),
        Long.parseUnsignedLong(attributes.getValue("Version"))
      );
  }

  @Override
  public NPPlanDescription onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPPlanDescription(
      this.identifier,
      this.timeouts,
      this.toolReferences,
      this.elements
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final Object result)
  {
    if (result instanceof final NPP1Tools tools) {
      for (final var tool : tools.tools()) {
        this.toolReferences.put(tool.referenceName(), tool);
      }
      return;
    }

    if (result instanceof final NPPlanTimeouts newTimeouts) {
      this.timeouts = newTimeouts;
      return;
    }

    if (result instanceof final NPPlanElementDescriptionType description) {
      this.elements.put(description.name(), description);
      return;
    }

    throw new IllegalStateException(
      "Unrecognized result: %s".formatted(result)
    );
  }
}
