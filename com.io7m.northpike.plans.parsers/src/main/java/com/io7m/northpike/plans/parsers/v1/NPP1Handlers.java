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
import com.io7m.blackthorne.core.Blackthorne;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.plans.NPPlanDescription;
import com.io7m.northpike.model.plans.NPPlanElementDescriptionType;
import com.io7m.northpike.model.plans.NPPlanToolExecution;
import com.io7m.verona.core.VersionParser;

import static com.io7m.blackthorne.core.BTIgnoreUnrecognizedElements.DO_NOT_IGNORE_UNRECOGNIZED_ELEMENTS;
import static com.io7m.northpike.plans.parsers.v1.NPP1.element;

/**
 * Handlers for v1 elements.
 */

public final class NPP1Handlers
{
  private NPP1Handlers()
  {

  }

  /**
   * @return A tool execution element parser
   */

  public static BTElementHandlerConstructorType<NPToolReferenceName, NPPlanToolExecution> toolExecution()
  {
    return NPP1ToolExecution::new;
  }

  /**
   * @return A tool requirement element parser
   */

  public static BTElementHandlerConstructorType<?, NPToolReferenceName> toolRequirement()
  {
    return Blackthorne.forScalarAttribute(
      element("ToolRequirement"),
      (context, attributes) -> {
        return NPToolReferenceName.of(attributes.getValue("ReferenceName"));
      }
    );
  }

  /**
   * @return A tool element parser
   */

  public static BTElementHandlerConstructorType<?, NPToolReference> tool()
  {
    return Blackthorne.forScalarAttribute(
      element("Tool"),
      (context, attributes) -> {
        return new NPToolReference(
          NPToolReferenceName.of(attributes.getValue("ReferenceName")),
          NPToolName.of(attributes.getValue("ToolName")),
          VersionParser.parse(attributes.getValue("ToolVersion"))
        );
      }
    );
  }

  /**
   * @return A tools element parser
   */

  public static BTElementHandlerConstructorType<?, NPP1Tools> tools()
  {
    return Blackthorne.mapConstructor(
      Blackthorne.forListMono(
        element("Tools"),
        element("Tool"),
        tool(),
        DO_NOT_IGNORE_UNRECOGNIZED_ELEMENTS
      ),
      NPP1Tools::new
    );
  }

  /**
   * @return A plan parser
   */

  public static BTElementHandlerConstructorType<?, NPPlanDescription> plan()
  {
    return NPP1Plan::new;
  }

  /**
   * @return A task parser
   */

  public static BTElementHandlerConstructorType<Object, NPPlanElementDescriptionType> task()
  {
    return NPP1Task::new;
  }

  /**
   * @return A barrier parser
   */

  public static BTElementHandlerConstructorType<Object, NPPlanElementDescriptionType> barrier()
  {
    return NPP1Barrier::new;
  }
}
