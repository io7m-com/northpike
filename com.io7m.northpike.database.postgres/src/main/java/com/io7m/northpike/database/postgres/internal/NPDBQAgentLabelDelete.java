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
import com.io7m.northpike.model.agents.NPAgentLabelName;
import org.jooq.DSLContext;
import org.jooq.Query;

import java.util.ArrayList;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABELS;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;
import static java.util.Map.entry;

/**
 * Delete an agent label.
 */

public final class NPDBQAgentLabelDelete
  extends NPDBQAbstract<Set<NPAgentLabelName>, NPDatabaseUnit>
  implements NPDatabaseQueriesAgentsType.AgentLabelDeleteType
{
  private static final Service<Set<NPAgentLabelName>, NPDatabaseUnit, AgentLabelDeleteType> SERVICE =
    new Service<>(AgentLabelDeleteType.class, NPDBQAgentLabelDelete::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentLabelDelete(
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
    final Set<NPAgentLabelName> labels)
  {
    final var statements =
      new ArrayList<Query>(labels.size() * 2);

    for (final var label : labels) {
      final var eqId =
        AGENT_LABELS.AL_LABEL.eq(AGENT_LABEL_DEFINITIONS.ALD_ID);
      final var eqName =
        AGENT_LABEL_DEFINITIONS.ALD_NAME.eq(label.toString());

      final var deleteAssociations =
        context.deleteFrom(AGENT_LABELS)
          .using(AGENT_LABEL_DEFINITIONS)
          .where(eqId.and(eqName));

      final var deleteLabel =
        context.deleteFrom(AGENT_LABEL_DEFINITIONS)
          .where(AGENT_LABEL_DEFINITIONS.ALD_NAME.eq(label.toString()));

      statements.add(deleteAssociations);
      statements.add(deleteLabel);
      statements.add(
        this.auditEvent(
          context,
          "AGENT_LABEL_DELETE",
          entry("NAME", label.toString())
        )
      );
    }

    context.batch(statements).execute();
    return UNIT;
  }
}
