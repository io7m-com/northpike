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

import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeDeleteType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentLoginChallengeGetType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPSignedData;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;

import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_AUTHENTICATION_ERROR_NO_SUCH_AGENT;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_AUTHENTICATION_ERROR_NO_SUCH_CHALLENGE;
import static com.io7m.northpike.strings.NPStringConstants.AGENT_AUTHENTICATION_ERROR_SIGNATURE_INVALID;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;

/**
 * @see com.io7m.northpike.protocol.agent.NPACommandCLoginComplete
 */

public final class NPACmdLoginComplete
  extends NPACmdAbstract<NPAResponseOK, NPACommandCLoginComplete>
{
  /**
   * @see NPACommandCLoginComplete
   */

  public NPACmdLoginComplete()
  {
    super(NPACommandCLoginComplete.class);
  }

  @Override
  public NPAResponseOK execute(
    final NPAgentCommandContextType context,
    final NPACommandCLoginComplete command)
    throws NPException
  {
    final var completion = command.completion();

    /*
     * Login succeeds iff:
     *
     * 1. An agent exists with the key given in the original login requests.
     *
     * 2. The signature the agent is presenting is a valid signature for the
     *    original data the server sent as a challenge.
     */

    final NPAgentDescription agent;
    try (var transaction = context.transaction()) {
      final var record =
        transaction.queries(AgentLoginChallengeGetType.class)
          .execute(completion.id())
          .orElseThrow(() -> {
            context.onAuthenticationFailed(
              Optional.empty(),
              AGENT_AUTHENTICATION_ERROR_NO_SUCH_CHALLENGE
            );
            return context.fail(ERROR_AUTHENTICATION, errorAuthentication());
          });

      agent = context.agentFindForKey(record.key())
        .orElseThrow(() -> {
          context.onAuthenticationFailed(
            Optional.of(record.key().id()),
            AGENT_AUTHENTICATION_ERROR_NO_SUCH_AGENT
          );
          return context.fail(ERROR_AUTHENTICATION, errorAuthentication());
        });

      final var signedData =
        new NPSignedData(
          record.challenge().data(),
          command.completion().signature()
        );

      final boolean verified;
      try {
        verified = record.key().verifyData(signedData);
      } catch (final NPException e) {
        NPTelemetryServiceType.recordSpanException(e);
        context.onAuthenticationFailed(
          Optional.of(record.key().id()),
          AGENT_AUTHENTICATION_ERROR_SIGNATURE_INVALID
        );
        throw context.fail(ERROR_AUTHENTICATION, errorAuthentication());
      }

      if (!verified) {
        context.onAuthenticationFailed(
          Optional.of(record.key().id()),
          AGENT_AUTHENTICATION_ERROR_SIGNATURE_INVALID
        );
        throw context.fail(ERROR_AUTHENTICATION, errorAuthentication());
      }

      transaction.queries(AgentLoginChallengeDeleteType.class)
        .execute(completion.id());
      transaction.commit();
    }

    context.onAuthenticationComplete(agent);
    return NPAResponseOK.createCorrelated(command);
  }
}
