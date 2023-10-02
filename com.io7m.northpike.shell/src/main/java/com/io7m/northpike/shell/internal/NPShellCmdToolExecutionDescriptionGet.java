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

import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionGet;
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
 * "tool-execution-get"
 */

public final class NPShellCmdToolExecutionDescriptionGet
  extends NPShellCmdAbstractCR<NPUCommandToolExecutionDescriptionGet, NPUResponseToolExecutionDescriptionGet>
{
  private static final QParameterNamed1<NPToolExecutionName> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The tool exection name."),
      Optional.empty(),
      NPToolExecutionName.class
    );

  private static final QParameterNamed1<Long> VERSION =
    new QParameterNamed1<>(
      "--version",
      List.of(),
      new QConstant("The tool exection version."),
      Optional.empty(),
      Long.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdToolExecutionDescriptionGet(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "tool-execution-get",
        new QConstant("Retrieve a tool execution."),
        Optional.empty()
      ),
      NPUCommandToolExecutionDescriptionGet.class,
      NPUResponseToolExecutionDescriptionGet.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(NAME, VERSION);
  }

  @Override
  protected NPUCommandToolExecutionDescriptionGet onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandToolExecutionDescriptionGet(
      UUID.randomUUID(),
      new NPToolExecutionIdentifier(
        context.parameterValue(NAME),
        context.parameterValue(VERSION).longValue()
      )
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseToolExecutionDescriptionGet response)
    throws Exception
  {
    final var opt = response.execution();
    if (opt.isPresent()) {
      final var data = opt.get();
      this.formatter().formatToolExecutionDescription(data);
    }
  }
}
