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

package com.io7m.northpike.agent.shell.internal;

import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentServerAssign;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
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
 * "agent-server-unassign"
 */

public final class NPAShellCmdAgentServerUnassign
  extends NPAShellCmdAbstractCR<NPACCommandAgentServerAssign, NPACResponseOK>
{
  private static final QParameterNamed1<NPAgentLocalName> AGENT =
    new QParameterNamed1<>(
      "--agent",
      List.of(),
      new QConstant(
        "The agent name."),
      Optional.empty(),
      NPAgentLocalName.class
    );

  private static final QParameterNamed1<NPAgentServerID> SERVER =
    new QParameterNamed1<>(
      "--server",
      List.of(),
      new QConstant(
        "The server ID."),
      Optional.empty(),
      NPAgentServerID.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The services
   */

  public NPAShellCmdAgentServerUnassign(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-server-unassign",
        new QConstant("Unassign a server from an agent."),
        Optional.empty()
      ),
      NPACCommandAgentServerAssign.class,
      NPACResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(AGENT);
  }

  @Override
  protected NPACCommandAgentServerAssign onCreateCommand(
    final QCommandContextType context)
  {
    return new NPACCommandAgentServerAssign(
      UUID.randomUUID(),
      context.parameterValue(AGENT),
      Optional.empty()
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPACResponseOK response)
    throws Exception
  {

  }
}
