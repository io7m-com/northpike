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
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.agents.NPAgentLabel;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import org.jooq.DSLContext;

import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LABEL_DEFINITIONS;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_LABEL;

/**
 * Retrieve an agent label.
 */

public final class NPDBQAgentLabelGet
  extends NPDBQAbstract<NPAgentLabelName, Optional<NPAgentLabel>>
  implements NPDatabaseQueriesAgentsType.AgentLabelGetType
{
  private static final Service<NPAgentLabelName, Optional<NPAgentLabel>, AgentLabelGetType> SERVICE =
    new Service<>(AgentLabelGetType.class, NPDBQAgentLabelGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentLabelGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPAgentLabel> onExecute(
    final DSLContext context,
    final NPAgentLabelName parameters)
    throws NPDatabaseException
  {
    this.setAttribute(AGENT_LABEL, parameters.toString());

    final var query =
      context.select(AGENT_LABEL_DEFINITIONS.ALD_DESCRIPTION)
        .from(AGENT_LABEL_DEFINITIONS)
        .where(AGENT_LABEL_DEFINITIONS.ALD_NAME.eq(parameters.toString()));

    recordQuery(query);
    return query.fetchOptional(AGENT_LABEL_DEFINITIONS.ALD_DESCRIPTION)
      .map(description -> new NPAgentLabel(parameters, description));
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
