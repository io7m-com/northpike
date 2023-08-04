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

import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPToolArguments;
import org.jooq.DSLContext;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.TOOL_ARGUMENTS;

/**
 * Update tool arguments.
 */

public final class NPDBQToolArgumentsPut
  extends NPDBQAbstract<NPToolArguments, NPDatabaseUnit>
  implements NPDatabaseQueriesToolsType.ArgumentsPutType
{
  private static final Service<NPToolArguments, NPDatabaseUnit, ArgumentsPutType> SERVICE =
    new Service<>(ArgumentsPutType.class, NPDBQToolArgumentsPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQToolArgumentsPut(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPToolArguments parameters)
    throws NPDatabaseException
  {
    final var argumentArray = new String[parameters.arguments().size()];
    parameters.arguments().toArray(argumentArray);

    final var query =
      context.insertInto(TOOL_ARGUMENTS)
        .set(TOOL_ARGUMENTS.TA_NAME, parameters.name().value())
        .set(TOOL_ARGUMENTS.TA_TOOL_NAME, parameters.toolName().value())
        .set(TOOL_ARGUMENTS.TA_ARGUMENTS, argumentArray)
        .onConflict(TOOL_ARGUMENTS.TA_NAME)
        .doUpdate()
        .set(TOOL_ARGUMENTS.TA_NAME, parameters.name().value())
        .set(TOOL_ARGUMENTS.TA_TOOL_NAME, parameters.toolName().value())
        .set(TOOL_ARGUMENTS.TA_ARGUMENTS, argumentArray);

    recordQuery(query);
    query.execute();
    return UNIT;
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
