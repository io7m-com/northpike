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

import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeAgentCreate;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "agent-login-challenge-agent-create"
 */

public final class NPShellCmdAgentLoginChallengeAgentCreate
  extends NPShellCmdAbstractCR<NPUCommandAgentLoginChallengeAgentCreate, NPUResponseOK>
{
  private static final QParameterNamed1<UUID> CHALLENGE_ID =
    new QParameterNamed1<>(
      "--challenge-id",
      List.of(),
      new QConstant("The ID of the login challenge record."),
      Optional.empty(),
      UUID.class
    );

  private static final QParameterNamed1<NPAgentID> AGENT_ID =
    new QParameterNamed1<>(
      "--agent-id",
      List.of(),
      new QConstant("The ID that will be used for the new agent."),
      Optional.empty(),
      NPAgentID.class
    );

  private static final QParameterNamed1<String> NAME =
    new QParameterNamed1<>(
      "--agent-name",
      List.of(),
      new QConstant("The name that will be used for the new agent."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentLoginChallengeAgentCreate(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-login-challenge-agent-create",
        new QConstant("Create an agent from a login challenge record."),
        Optional.empty()
      ),
      NPUCommandAgentLoginChallengeAgentCreate.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      CHALLENGE_ID,
      AGENT_ID,
      NAME
    );
  }

  @Override
  protected NPUCommandAgentLoginChallengeAgentCreate onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandAgentLoginChallengeAgentCreate(
      UUID.randomUUID(),
      context.parameterValue(CHALLENGE_ID),
      context.parameterValue(AGENT_ID),
      context.parameterValue(NAME)
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseOK response)
    throws Exception
  {

  }
}
