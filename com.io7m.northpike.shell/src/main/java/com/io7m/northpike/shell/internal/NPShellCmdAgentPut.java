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

package com.io7m.northpike.shell.internal;

import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.protocol.user.NPUCommandAgentGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentPut;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "agent-put"
 */

public final class NPShellCmdAgentPut extends NPShellCmdAbstractU
{
  private static final QParameterNamed1<NPAgentID> AGENT_ID =
    new QParameterNamed1<>(
      "--id",
      List.of(),
      new QConstant("The agent ID."),
      Optional.empty(),
      NPAgentID.class
    );

  private static final QParameterNamed1<String> AGENT_NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The agent name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed1<NPAgentKeyPublicType> AGENT_PUBLIC_KEY =
    new QParameterNamed1<>(
      "--public-key",
      List.of(),
      new QConstant("The agent public key."),
      Optional.empty(),
      NPAgentKeyPublicType.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentPut(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-put",
        new QConstant("Create/update a agent."),
        Optional.empty()
      )
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      AGENT_ID,
      AGENT_NAME,
      AGENT_PUBLIC_KEY
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var client =
      this.client();

    final var rGet =
      client.execute(
        new NPUCommandAgentGet(
          UUID.randomUUID(),
          context.parameterValue(AGENT_ID)
        )
      );

    final var newAgent =
      rGet.agent()
        .map(existing -> {
          return new NPAgentDescription(
            existing.id(),
            context.parameterValue(AGENT_NAME),
            context.parameterValue(AGENT_PUBLIC_KEY),
            existing.environmentVariables(),
            existing.systemProperties(),
            existing.labels()
          );
        })
        .orElse(new NPAgentDescription(
          context.parameterValue(AGENT_ID),
          context.parameterValue(AGENT_NAME),
          context.parameterValue(AGENT_PUBLIC_KEY),
          Map.of(),
          Map.of(),
          Map.of()
        ));

    client.execute(new NPUCommandAgentPut(UUID.randomUUID(), newAgent));
    return SUCCESS;
  }
}
