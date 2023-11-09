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

import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerList;
import com.io7m.northpike.protocol.agent_console.NPACResponseServerList;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "server-list"
 */

public final class NPAShellCmdServerList
  extends NPAShellCmdAbstractCR<NPACCommandServerList, NPACResponseServerList>
{
  private static final QParameterNamed01<NPAgentServerID> OFFSET =
    new QParameterNamed01<>(
      "--offset",
      List.of(),
      new QConstant(
        "The starting server offset."),
      Optional.empty(),
      NPAgentServerID.class
    );

  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant(
        "Limit the number of returned results."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The services
   */

  public NPAShellCmdServerList(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "server-list",
        new QConstant("List servers."),
        Optional.empty()
      ),
      NPACCommandServerList.class,
      NPACResponseServerList.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      OFFSET,
      LIMIT
    );
  }

  @Override
  protected NPACCommandServerList onCreateCommand(
    final QCommandContextType context)
  {
    return new NPACCommandServerList(
      UUID.randomUUID(),
      context.parameterValue(OFFSET),
      context.<Integer>parameterValue(LIMIT).longValue()
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPACResponseServerList response)
    throws Exception
  {
    this.formatter().formatServerSummaries(response.results());
  }
}
