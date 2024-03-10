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

import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.LoginChallengeGetForKeyType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentKeyPairEd448Type;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import org.jooq.DSLContext;

import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.Tables.AGENT_LOGIN_CHALLENGES;

/**
 * Get an agent login challenge.
 */

public final class NPDBQAgentLoginChallengeGetForKey
  extends NPDBQAbstract<NPAgentKeyPublicType, Optional<NPAgentLoginChallengeRecord>>
  implements LoginChallengeGetForKeyType
{
  private static final Service<
    NPAgentKeyPublicType,
    Optional<NPAgentLoginChallengeRecord>,
    LoginChallengeGetForKeyType> SERVICE =
    new Service<>(
      LoginChallengeGetForKeyType.class,
      NPDBQAgentLoginChallengeGetForKey::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAgentLoginChallengeGetForKey(
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
  protected Optional<NPAgentLoginChallengeRecord> onExecute(
    final DSLContext context,
    final NPAgentKeyPublicType data)
    throws NPException
  {
    final var query =
      context.select(
          AGENT_LOGIN_CHALLENGES.ALC_CHALLENGE,
          AGENT_LOGIN_CHALLENGES.ALC_CREATED,
          AGENT_LOGIN_CHALLENGES.ALC_ID,
          AGENT_LOGIN_CHALLENGES.ALC_KEY_ALGO,
          AGENT_LOGIN_CHALLENGES.ALC_KEY_DATA,
          AGENT_LOGIN_CHALLENGES.ALC_SOURCE
        ).from(AGENT_LOGIN_CHALLENGES)
        .where(
          AGENT_LOGIN_CHALLENGES.ALC_KEY_ALGO.eq(data.algorithm())
            .and(AGENT_LOGIN_CHALLENGES.ALC_KEY_DATA.eq(data.asText()))
        );

    recordQuery(query);

    final var r = query.fetchOptional();
    if (r.isPresent()) {
      return Optional.of(mapRecord(r.get()));
    }
    return Optional.empty();
  }

  private static NPAgentLoginChallengeRecord mapRecord(
    final org.jooq.Record r)
    throws NPException
  {
    final var algorithm =
      r.get(AGENT_LOGIN_CHALLENGES.ALC_KEY_ALGO);

    final var key =
      switch (algorithm) {
        case NPAgentKeyPairEd448Type.ALGORITHM_NAME -> {
          yield new NPAgentKeyPairFactoryEd448()
            .parsePublicKeyFromText(r.get(AGENT_LOGIN_CHALLENGES.ALC_KEY_DATA));
        }
        default -> {
          throw new IllegalStateException(
            "Unrecognized key algorithm: %s".formatted(algorithm)
          );
        }
      };

    return new NPAgentLoginChallengeRecord(
      r.get(AGENT_LOGIN_CHALLENGES.ALC_CREATED),
      r.get(AGENT_LOGIN_CHALLENGES.ALC_SOURCE),
      key,
      new NPAgentLoginChallenge(
        r.get(AGENT_LOGIN_CHALLENGES.ALC_ID),
        r.get(AGENT_LOGIN_CHALLENGES.ALC_CHALLENGE)
      )
    );
  }
}
