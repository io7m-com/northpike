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

import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.DeleteExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.tables.ToolExecutionDescriptions.TOOL_EXECUTION_DESCRIPTIONS;
import static java.util.Map.entry;

/**
 * Delete a tool execution description.
 */

public final class NPDBQToolExecutionDescriptionDelete
  extends NPDBQAbstract<NPToolExecutionIdentifier, NPDatabaseUnit>
  implements DeleteExecutionDescriptionType
{
  private static final Service<NPToolExecutionIdentifier, NPDatabaseUnit, DeleteExecutionDescriptionType> SERVICE =
    new Service<>(
      DeleteExecutionDescriptionType.class,
      NPDBQToolExecutionDescriptionDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQToolExecutionDescriptionDelete(
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
    final NPToolExecutionIdentifier d)
  {
    final var nameMatches =
      TOOL_EXECUTION_DESCRIPTIONS.TED_NAME.eq(d.name().toString());
    final var versionMatches =
      TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION.eq(Long.valueOf(d.version()));

    context.deleteFrom(TOOL_EXECUTION_DESCRIPTIONS)
      .where(nameMatches.and(versionMatches))
      .execute();

    this.auditEventPut(
      context,
      "TOOL_EXECUTION_DELETE",
      entry("TOOL_EXECUTION_NAME", d.name().toString()),
      entry("TOOL_EXECUTION_VERSION", Long.toUnsignedString(d.version()))
    );
    return UNIT;
  }
}
