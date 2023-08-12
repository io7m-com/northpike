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

package com.io7m.northpike.database.postgres.internal;

import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.PutExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPToolExecutionDescription;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.tables.ToolExecutionDescriptions.TOOL_EXECUTION_DESCRIPTIONS;

/**
 * Update a tool execution description.
 */

public final class NPDBQToolExecutionDescriptionPut
  extends NPDBQAbstract<NPToolExecutionDescription, NPDatabaseUnit>
  implements PutExecutionDescriptionType
{
  private static final Service<NPToolExecutionDescription, NPDatabaseUnit, PutExecutionDescriptionType> SERVICE =
    new Service<>(
      PutExecutionDescriptionType.class,
      NPDBQToolExecutionDescriptionPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQToolExecutionDescriptionPut(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPToolExecutionDescription d)
  {
    final var id = d.identifier();
    context.insertInto(TOOL_EXECUTION_DESCRIPTIONS)
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_NAME, id.name().value())
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION, Long.valueOf(id.version()))
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_FORMAT, d.format().value())
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME, d.tool().value())
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_TEXT, d.text())
      .onConflictOnConstraint(
        DSL.name("tool_execution_descriptions_name_version_unique"))
      .doUpdate()
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_FORMAT, d.format().value())
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME, d.tool().value())
      .set(TOOL_EXECUTION_DESCRIPTIONS.TED_TEXT, d.text())
      .execute();
    return UNIT;
  }
}
