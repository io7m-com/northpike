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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPToolArguments;
import org.jooq.DSLContext;
import org.jooq.Record3;

import java.util.List;
import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.Tables.TOOL_ARGUMENTS;

/**
 * Retrieve tool arguments.
 */

public final class NPDBQToolArgumentsGet
  extends NPDBQAbstract<RDottedName, Optional<NPToolArguments>>
  implements NPDatabaseQueriesToolsType.ArgumentsGetType
{
  private static final Service<RDottedName, Optional<NPToolArguments>, ArgumentsGetType> SERVICE =
    new Service<>(ArgumentsGetType.class, NPDBQToolArgumentsGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQToolArgumentsGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPToolArguments> onExecute(
    final DSLContext context,
    final RDottedName parameters)
    throws NPDatabaseException
  {
    return context.select(
        TOOL_ARGUMENTS.TA_NAME,
        TOOL_ARGUMENTS.TA_TOOL_NAME,
        TOOL_ARGUMENTS.TA_ARGUMENTS)
      .from(TOOL_ARGUMENTS)
      .where(TOOL_ARGUMENTS.TA_NAME.eq(parameters.value()))
      .fetchOptional()
      .map(NPDBQToolArgumentsGet::mapRecord);
  }

  private static NPToolArguments mapRecord(
    final Record3<String, String, String[]> r)
  {
    return new NPToolArguments(
      new RDottedName(r.get(TOOL_ARGUMENTS.TA_NAME)),
      new RDottedName(r.get(TOOL_ARGUMENTS.TA_TOOL_NAME)),
      List.of(r.get(TOOL_ARGUMENTS.TA_ARGUMENTS))
    );
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
