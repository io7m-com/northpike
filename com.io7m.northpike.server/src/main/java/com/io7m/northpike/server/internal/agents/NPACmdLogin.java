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


package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.clock.NPClockServiceType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.LoginChallengeGetForKeyType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.LoginChallengePutType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;

/**
 * @see NPACommandCLogin
 */

public final class NPACmdLogin
  extends NPACmdAbstract<NPAResponseLoginChallenge, NPACommandCLogin>
{
  /**
   * @see NPACommandCLogin
   */

  public NPACmdLogin()
  {
    super(NPACommandCLogin.class);
  }

  @Override
  public NPAResponseLoginChallenge execute(
    final NPAgentCommandContextType context,
    final NPACommandCLogin command)
    throws NPException
  {
    final var services =
      context.services();
    final var clock =
      services.requireService(NPClockServiceType.class);

    final var agentOpt =
      context.agentFindForKey(command.key());

    /*
     * Create a login challenge. Note that the challenge is created even if
     * the agent does not exist; the administrator can use the information in
     * the challenge record to create a new agent description in the database.
     * We avoid creating multiple login challenges for the same public key.
     */

    final NPAgentLoginChallengeRecord challenge;
    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var existingChallenge =
          transaction.queries(LoginChallengeGetForKeyType.class)
            .execute(command.key());

        challenge = existingChallenge.orElseGet(() -> {
          return new NPAgentLoginChallengeRecord(
            clock.now(),
            context.sourceAddress(),
            command.key(),
            NPAgentLoginChallenge.generate()
          );
        });

        transaction.queries(LoginChallengePutType.class).execute(challenge);
        transaction.commit();
      }
    }

    if (agentOpt.isEmpty()) {
      throw context.fail(ERROR_AUTHENTICATION, errorAuthentication());
    }

    return NPAResponseLoginChallenge.createCorrelated(
      command,
      challenge.challenge()
    );
  }
}
