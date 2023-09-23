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

import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPAgentLabel;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_LABEL;
import static java.util.Map.entry;

/**
 * Update an agent label.
 */

public final class NPDBQAgentLabelPut
  extends NPDBQAbstract<NPAgentLabel, NPDatabaseUnit>
  implements NPDatabaseQueriesAgentsType.LabelPutType
{
  private static final Service<NPAgentLabel, NPDatabaseUnit, LabelPutType> SERVICE =
    new Service<>(LabelPutType.class, NPDBQAgentLabelPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentLabelPut(
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
    final NPAgentLabel label)
  {
    this.setAttribute(AGENT_LABEL, label.name().value());

    final var query =
      context.insertInto(AGENT_LABEL_DEFINITIONS)
        .set(AGENT_LABEL_DEFINITIONS.ALD_NAME, label.name().value())
        .set(AGENT_LABEL_DEFINITIONS.ALD_DESCRIPTION, label.description())
        .onConflictOnConstraint(DSL.name("agent_label_definitions_name_unique"))
        .doUpdate()
        .set(AGENT_LABEL_DEFINITIONS.ALD_DESCRIPTION, label.description());

    recordQuery(query);
    query.execute();

    this.auditEventPut(
      context,
      "AGENT_LABEL_PUT",
      entry("NAME", label.name().value())
    );
    return UNIT;
  }
}
