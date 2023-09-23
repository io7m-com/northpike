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
import com.io7m.northpike.model.NPAgentDescription;
import org.jooq.DSLContext;
import org.jooq.Query;

import java.util.ArrayList;
import java.util.Map;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENTS_PROPERTIES;
import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;
import static com.io7m.northpike.database.postgres.internal.tables.AgentLabels.AGENT_LABELS;
import static com.io7m.northpike.database.postgres.internal.tables.AgentsEnvironments.AGENTS_ENVIRONMENTS;
import static com.io7m.northpike.strings.NPStringConstants.AGENT;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_ID;

/**
 * Update an agent.
 */

public final class NPDBQAgentPut
  extends NPDBQAbstract<NPAgentDescription, NPDatabaseUnit>
  implements NPDatabaseQueriesAgentsType.PutType
{
  private static final Service<NPAgentDescription, NPDatabaseUnit, PutType> SERVICE =
    new Service<>(PutType.class, NPDBQAgentPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentPut(
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
    final NPAgentDescription agent)
  {
    this.setAttribute(AGENT, agent.name());
    final var agentId = agent.id().value();
    this.setAttribute(AGENT_ID, agentId.toString());

    final var batches = new ArrayList<Query>();
    batches.add(
      context.deleteFrom(AGENTS_ENVIRONMENTS)
        .where(AGENTS_ENVIRONMENTS.AE_ID.eq(agentId))
    );
    batches.add(
      context.deleteFrom(AGENTS_PROPERTIES)
        .where(AGENTS_PROPERTIES.AP_ID.eq(agentId))
    );
    batches.add(
      context.deleteFrom(AGENT_LABELS)
        .where(AGENT_LABELS.AL_AGENT.eq(agentId))
    );

    batches.add(
      context.insertInto(AGENTS)
        .set(AGENTS.A_ID, agentId)
        .set(AGENTS.A_ACCESS_KEY, agent.accessKey().format())
        .set(AGENTS.A_NAME, agent.name())
        .onConflict(AGENTS.A_ID)
        .doUpdate()
        .set(AGENTS.A_ACCESS_KEY, agent.accessKey().format())
        .set(AGENTS.A_NAME, agent.name())
    );

    for (final var entry : agent.environmentVariables().entrySet()) {
      batches.add(
        context.insertInto(AGENTS_ENVIRONMENTS)
          .set(AGENTS_ENVIRONMENTS.AE_ID, agentId)
          .set(AGENTS_ENVIRONMENTS.AE_NAME, entry.getKey())
          .set(AGENTS_ENVIRONMENTS.AE_VALUE, entry.getValue())
      );
    }
    for (final var entry : agent.systemProperties().entrySet()) {
      batches.add(
        context.insertInto(AGENTS_PROPERTIES)
          .set(AGENTS_PROPERTIES.AP_ID, agentId)
          .set(AGENTS_PROPERTIES.AP_NAME, entry.getKey())
          .set(AGENTS_PROPERTIES.AP_VALUE, entry.getValue())
      );
    }
    for (final var entry : agent.labels().values()) {
      final var labelId =
        context.select(AGENT_LABEL_DEFINITIONS.ALD_ID)
          .from(AGENT_LABEL_DEFINITIONS)
          .where(AGENT_LABEL_DEFINITIONS.ALD_NAME.eq(entry.name().value()));

      batches.add(
        context.insertInto(AGENT_LABELS)
          .set(AGENT_LABELS.AL_AGENT, agentId)
          .set(AGENT_LABELS.AL_LABEL, labelId)
      );
    }

    batches.add(this.auditEvent(
      context,
      "AGENT_PUT",
      Map.entry("AGENT", agentId.toString()))
    );

    recordQuery(batches);
    context.batch(batches).execute();
    return UNIT;
  }
}
