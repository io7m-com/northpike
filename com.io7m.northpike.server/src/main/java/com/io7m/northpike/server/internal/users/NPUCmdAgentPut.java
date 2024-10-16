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
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentGetType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesAgentsType.AgentPutType;
import com.io7m.northpike.model.NPAuditOwnerType.User;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandAgentPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.security.NPSecurity;

import java.util.Map;

/**
 * @see NPUCommandAgentPut
 */

public final class NPUCmdAgentPut
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandAgentPut>
{
  /**
   * @see NPUCommandAgentPut
   */

  public NPUCmdAgentPut()
  {
    super(NPUCommandAgentPut.class);
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandAgentPut command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.AGENTS.object(),
      NPSecAction.WRITE.action()
    );

    try (var transaction = context.transaction()) {
      transaction.setOwner(new User(user.userId()));

      final var givenAgent =
        command.agent();
      final var existing =
        transaction.queries(AgentGetType.class)
          .execute(new Parameters(givenAgent.id(), false));

      /*
       * The environment variables and system properties are
       * ignored for the incoming agent. The environment and system properties
       * are set via agents upon authenticating.
       */

      final NPAgentDescription savedAgent;
      if (existing.isPresent()) {
        final var existingAgent = existing.get();
        savedAgent = new NPAgentDescription(
          givenAgent.id(),
          givenAgent.name(),
          givenAgent.publicKey(),
          existingAgent.environmentVariables(),
          existingAgent.systemProperties(),
          givenAgent.labels()
        );
      } else {
        savedAgent = new NPAgentDescription(
          givenAgent.id(),
          givenAgent.name(),
          givenAgent.publicKey(),
          Map.of(),
          Map.of(),
          givenAgent.labels()
        );
      }

      transaction.queries(AgentPutType.class).execute(savedAgent);
      transaction.commit();
    }

    return NPUResponseOK.createCorrelated(command);
  }
}
