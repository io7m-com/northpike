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


package com.io7m.northpike.agent.expressions;

import com.io7m.jxe.core.JXESchemaDefinition;
import com.io7m.jxe.core.JXESchemaResolutionMappings;

import java.net.URI;

/**
 * Configuration XML schemas.
 */

public final class NAESchemas
{
  private static final JXESchemaDefinition LABEL_EXPRESSIONS_SCHEMA_1 =
    JXESchemaDefinition.builder()
      .setFileIdentifier("toolexec-1.xsd")
      .setLocation(NAESchemas.class.getResource(
        "/com/io7m/northpike/agent/expressions/agent-label-expressions-1.xsd"))
      .setNamespace(URI.create("urn:com.io7m.northpike.agent.label_expressions:1"))
      .build();

  private static final JXESchemaResolutionMappings LABEL_EXPRESSIONS_SCHEMA_MAPPINGS =
    JXESchemaResolutionMappings.builder()
      .putMappings(
        LABEL_EXPRESSIONS_SCHEMA_1.namespace(),
        LABEL_EXPRESSIONS_SCHEMA_1)
      .build();

  /**
   * @return The 1 schema
   */

  public static JXESchemaDefinition labelExpressions1()
  {
    return LABEL_EXPRESSIONS_SCHEMA_1;
  }

  /**
   * @return The set of supported schemas.
   */

  public static JXESchemaResolutionMappings labelExpressions()
  {
    return LABEL_EXPRESSIONS_SCHEMA_MAPPINGS;
  }

  private NAESchemas()
  {

  }
}
