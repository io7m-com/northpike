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
import com.io7m.northpike.protocol.user.NPUCommandAgentDelete;
import com.io7m.northpike.shell.commons.NPShellCmdAbstractConfirmationRequired;
import com.io7m.northpike.shell.commons.NPShellConfirmationRequest;
import com.io7m.northpike.user_client.api.NPUserClientType;
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
 * "agent-delete"
 */

public final class NPShellCmdAgentDelete
  extends NPShellCmdAbstractConfirmationRequired
{
  private static final QParameterNamed1<NPAgentID> AGENT_ID =
    new QParameterNamed1<>(
      "--id",
      List.of(),
      new QConstant("The agent ID."),
      Optional.empty(),
      NPAgentID.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentDelete(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-delete",
        new QConstant("Delete an agent."),
        Optional.empty()
      )
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParametersConfirmed()
  {
    return List.of(
      AGENT_ID
    );
  }

  @Override
  protected NPShellConfirmationRequest onRequireConfirmation(
    final QCommandContextType context)
  {
    return new NPShellConfirmationRequest(
      "agent-delete-confirm",
      () -> {
        final var client =
          this.services().requireService(NPUserClientType.class);

        client.execute(new NPUCommandAgentDelete(
          UUID.randomUUID(),
          context.parameterValue(AGENT_ID)
        ));
      }
    );
  }
}
