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
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.plans.NPPlanToolExecution;
import org.xml.sax.Attributes;

import java.util.Map;
import java.util.TreeSet;

import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * A parser for tool execution elements.
 */

public final class NPP1ToolExecution
  implements BTElementHandlerType<NPToolReferenceName, NPPlanToolExecution>
{
  private final TreeSet<NPToolReferenceName> requirements;
  private NPToolReferenceName referenceName;
  private NPToolExecutionName executionName;
  private long executionVersion;

  /**
   * A parser for tool execution elements.
   *
   * @param context The parse context
   */

  public NPP1ToolExecution(
    final BTElementParsingContextType context)
  {
    this.requirements = new TreeSet<>();
  }

  @Override
  public Map<BTQualifiedName, BTElementHandlerConstructorType<?, ? extends NPToolReferenceName>>
  onChildHandlersRequested(
    final BTElementParsingContextType context)
  {
    return Map.ofEntries(
      Map.entry(
        element("ToolRequirement"),
        NPP1Handlers.toolRequirement()
      )
    );
  }

  @Override
  public void onElementStart(
    final BTElementParsingContextType context,
    final Attributes attributes)
  {
    this.referenceName =
      NPToolReferenceName.of(attributes.getValue("ReferenceName"));
    this.executionName =
      NPToolExecutionName.of(attributes.getValue("ExecutionName"));
    this.executionVersion =
      Long.parseUnsignedLong(attributes.getValue("ExecutionVersion"));
  }

  @Override
  public NPPlanToolExecution onElementFinished(
    final BTElementParsingContextType context)
  {
    return new NPPlanToolExecution(
      this.referenceName,
      new NPToolExecutionIdentifier(
        this.executionName,
        this.executionVersion
      ),
      this.requirements
    );
  }

  @Override
  public void onChildValueProduced(
    final BTElementParsingContextType context,
    final NPToolReferenceName result)
  {
    this.requirements.add(result);
  }
}
