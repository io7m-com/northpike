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
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.GetExecutionDescriptionType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import org.jooq.DSLContext;
import org.jooq.Record5;

import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.Tables.TOOL_EXECUTION_DESCRIPTIONS;

/**
 * Retrieve a tool execution description.
 */

public final class NPDBQToolExecutionDescriptionGet
  extends NPDBQAbstract<NPToolExecutionIdentifier, Optional<NPToolExecutionDescription>>
  implements GetExecutionDescriptionType
{
  private static final Service<
    NPToolExecutionIdentifier,
    Optional<NPToolExecutionDescription>,
    GetExecutionDescriptionType
    > SERVICE =
    new Service<>(
      GetExecutionDescriptionType.class,
      NPDBQToolExecutionDescriptionGet::new
    );

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQToolExecutionDescriptionGet(
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
  protected Optional<NPToolExecutionDescription> onExecute(
    final DSLContext context,
    final NPToolExecutionIdentifier id)
    throws NPDatabaseException
  {
    final var condition =
      TOOL_EXECUTION_DESCRIPTIONS.TED_NAME.eq(id.name().toString())
        .and(TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION.eq(Long.valueOf(id.version())));

    return context.select(
        TOOL_EXECUTION_DESCRIPTIONS.TED_NAME,
        TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION,
        TOOL_EXECUTION_DESCRIPTIONS.TED_FORMAT,
        TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME,
        TOOL_EXECUTION_DESCRIPTIONS.TED_TEXT
      ).from(TOOL_EXECUTION_DESCRIPTIONS)
      .where(condition)
      .fetchOptional()
      .map(NPDBQToolExecutionDescriptionGet::mapRecord);
  }

  private static NPToolExecutionDescription mapRecord(
    final Record5<String, Long, String, String, String> r)
  {
    return new NPToolExecutionDescription(
      new NPToolExecutionIdentifier(
        NPToolExecutionName.of(r.get(TOOL_EXECUTION_DESCRIPTIONS.TED_NAME)),
        r.<Long>get(TOOL_EXECUTION_DESCRIPTIONS.TED_VERSION).longValue()
      ),
      NPToolName.of(r.get(TOOL_EXECUTION_DESCRIPTIONS.TED_TOOL_NAME)),
      NPFormatName.of(r.get(TOOL_EXECUTION_DESCRIPTIONS.TED_FORMAT)),
      r.get(TOOL_EXECUTION_DESCRIPTIONS.TED_TEXT)
    );
  }
}
