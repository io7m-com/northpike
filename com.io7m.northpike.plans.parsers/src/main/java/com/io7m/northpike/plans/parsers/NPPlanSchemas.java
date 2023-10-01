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


package com.io7m.northpike.plans.parsers;

import com.io7m.jxe.core.JXESchemaDefinition;
import com.io7m.jxe.core.JXESchemaResolutionMappings;

import java.net.URI;

/**
 * Configuration XML schemas.
 */

public final class NPPlanSchemas
{
  private static final JXESchemaDefinition PLANS_SCHEMA_1 =
    JXESchemaDefinition.builder()
      .setFileIdentifier("plans-1.xsd")
      .setLocation(NPPlanSchemas.class.getResource(
        "/com/io7m/northpike/plans/parsers/plans-1.xsd"))
      .setNamespace(URI.create("urn:com.io7m.northpike.plans:1"))
      .build();

  private static final JXESchemaResolutionMappings PLANS_SCHEMA_MAPPINGS =
    JXESchemaResolutionMappings.builder()
      .putMappings(PLANS_SCHEMA_1.namespace(), PLANS_SCHEMA_1)
      .build();

  /**
   * @return The 1 schema
   */

  public static JXESchemaDefinition plans1()
  {
    return PLANS_SCHEMA_1;
  }

  /**
   * @return The set of supported schemas.
   */

  public static JXESchemaResolutionMappings plans()
  {
    return PLANS_SCHEMA_MAPPINGS;
  }

  private NPPlanSchemas()
  {

  }
}
