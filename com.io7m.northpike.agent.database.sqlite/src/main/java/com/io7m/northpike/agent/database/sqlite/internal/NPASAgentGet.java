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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import org.jooq.DSLContext;

import java.util.Optional;

import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;

/**
 * Retrieve an agent.
 */

public final class NPASAgentGet
  extends NPASQAbstract<NPAgentLocalName, Optional<NPAgentLocalDescription>>
  implements NPAgentDatabaseQueriesAgentsType.AgentGetType
{
  private static final Service<NPAgentLocalName, Optional<NPAgentLocalDescription>, AgentGetType> SERVICE =
    new Service<>(AgentGetType.class, NPASAgentGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentGet(
    final NPASTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPASQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected Optional<NPAgentLocalDescription> onExecute(
    final DSLContext context,
    final NPAgentLocalName agent)
    throws NPAgentDatabaseException
  {
    final var result =
      context.select(
          AGENTS.A_NAME,
          AGENTS.A_KEY_PRIVATE,
          AGENTS.A_KEY_ALGO,
          AGENTS.A_KEY_PUBLIC
        ).from(AGENTS)
        .where(AGENTS.A_NAME.eq(agent.toString()))
        .fetchOptional();

    if (result.isPresent()) {
      return Optional.of(mapRecord(result.get()));
    }
    return Optional.empty();
  }

  private static NPAgentLocalDescription mapRecord(
    final org.jooq.Record record)
    throws NPAgentDatabaseException
  {
    final var algorithm =
      record.get(AGENTS.A_KEY_ALGO);

    final var keyPair =
      switch (algorithm) {
        case NPAgentKeyPairEd448Type.ALGORITHM_NAME -> {
          try {
            yield new NPAgentKeyPairFactoryEd448()
              .parseFromText(
                record.get(AGENTS.A_KEY_PUBLIC),
                record.get(AGENTS.A_KEY_PRIVATE)
              );
          } catch (final NPException e) {
            throw new NPAgentDatabaseException(
              e.getMessage(),
              e,
              e.errorCode(),
              e.attributes(),
              e.remediatingAction()
            );
          }
        }
        default -> {
          throw new IllegalStateException(
            "Unrecognized algorithm: %s".formatted(algorithm)
          );
        }
      };

    return new NPAgentLocalDescription(
      NPAgentLocalName.of(record.get(AGENTS.A_NAME)),
      keyPair
    );
  }
}
