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

import com.io7m.northpike.model.NPAgentDescription;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.protocol.user.NPUCommandAgentGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentPut;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed0N;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "agent-label-unassign"
 */

public final class NPShellCmdAgentLabelUnassign extends NPShellCmdAbstract
{
  private static final QParameterNamed1<NPAgentID> AGENT_ID =
    new QParameterNamed1<>(
      "--agent",
      List.of(),
      new QConstant("The agent ID."),
      Optional.empty(),
      NPAgentID.class
    );

  private static final QParameterNamed0N<NPAgentLabelName> LABEL_NAME =
    new QParameterNamed0N<>(
      "--label",
      List.of(),
      new QConstant("The label name."),
      List.of(),
      NPAgentLabelName.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentLabelUnassign(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-label-unassign",
        new QConstant("Unassign labels from an agent."),
        Optional.empty()
      )
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      AGENT_ID,
      LABEL_NAME
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var client =
      this.client();
    final var agentId =
      context.parameterValue(AGENT_ID);

    this.setAttribute(NPStringConstants.AGENT_ID, agentId);

    final var rGet =
      client.execute(new NPUCommandAgentGet(UUID.randomUUID(), agentId));

    final var existing = rGet.agent();
    if (existing.isEmpty()) {
      throw this.fail(errorNonexistent(), ERROR_NONEXISTENT);
    }

    final var existingAgent =
      existing.get();
    final var existingLabels =
      new HashMap<>(existingAgent.labels());

    for (final var label : context.parameterValues(LABEL_NAME)) {
      existingLabels.remove(label);
    }

    final var newAgent =
      new NPAgentDescription(
        existingAgent.id(),
        existingAgent.name(),
        existingAgent.accessKey(),
        Map.of(),
        Map.of(),
        existingLabels
      );

    client.execute(new NPUCommandAgentPut(UUID.randomUUID(), newAgent));
    return SUCCESS;
  }
}
