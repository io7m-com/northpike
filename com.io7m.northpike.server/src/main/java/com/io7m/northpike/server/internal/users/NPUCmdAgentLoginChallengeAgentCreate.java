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


package com.io7m.northpike.server.internal.users;

import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeDeleteType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeAgentCreate;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.strings.NPStrings;

import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorDuplicate;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_ID;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_DUPLICATE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.northpike.strings.NPStringConstants.LOGIN_CHALLENGE;
import static java.util.Map.entry;

/**
 * @see NPUCommandAgentLoginChallengeAgentCreate
 */

public final class NPUCmdAgentLoginChallengeAgentCreate
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandAgentLoginChallengeAgentCreate>
{
  /**
   * @see NPUCommandAgentLoginChallengeAgentCreate
   */

  public NPUCmdAgentLoginChallengeAgentCreate()
  {
    super(NPUCommandAgentLoginChallengeAgentCreate.class);
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandAgentLoginChallengeAgentCreate command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.AGENT_LOGIN_CHALLENGES.object(),
      NPSecAction.READ.action()
    );
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.AGENT_LOGIN_CHALLENGES.object(),
      NPSecAction.DELETE.action()
    );
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.AGENTS.object(),
      NPSecAction.WRITE.action()
    );

    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        transaction.setOwner(new NPAuditOwnerType.User(user.userId()));

        /*
         * We want to include deleted agents so that we don't try to create
         * a "new" agent with the same ID.
         */

        final var existingAgent =
          transaction.queries(AgentGetType.class)
            .execute(new AgentGetType.Parameters(command.agent(), true));

        if (existingAgent.isPresent()) {
          throw errorAgentAlreadyExists(context, command.agent());
        }

        final var existingChallenge =
          transaction.queries(AgentLoginChallengeGetType.class)
            .execute(command.loginChallenge())
            .orElseThrow(() -> {
              return errorNoSuchChallenge(context, command.loginChallenge());
            });

        transaction.queries(AgentPutType.class)
          .execute(new NPAgentDescription(
            command.agent(),
            command.name(),
            existingChallenge.key(),
            Map.of(),
            Map.of(),
            Map.of()
          ));

        transaction.queries(AgentLoginChallengeDeleteType.class)
          .execute(command.loginChallenge());

        transaction.commit();
        return NPUResponseOK.createCorrelated(command);
      }
    }
  }

  private static NPException errorNoSuchChallenge(
    final NPUserCommandContextType context,
    final UUID challenge)
  {
    final var strings =
      context.services()
        .requireService(NPStrings.class);

    return new NPException(
      strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        entry(strings.format(LOGIN_CHALLENGE), challenge.toString())
      ),
      Optional.empty()
    );
  }

  private static NPException errorAgentAlreadyExists(
    final NPUserCommandContextType context,
    final NPAgentID agent)
  {
    final var strings =
      context.services()
        .requireService(NPStrings.class);

    return new NPException(
      strings.format(ERROR_DUPLICATE),
      errorDuplicate(),
      Map.ofEntries(
        entry(strings.format(AGENT_ID), agent.toString())
      ),
      Optional.empty()
    );
  }
}
