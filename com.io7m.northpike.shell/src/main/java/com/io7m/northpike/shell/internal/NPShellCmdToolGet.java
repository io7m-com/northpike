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

import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.protocol.user.NPUCommandToolGet;
import com.io7m.northpike.protocol.user.NPUResponseToolGet;
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
 * "tool-get"
 */

public final class NPShellCmdToolGet
  extends NPShellCmdAbstractCR<NPUCommandToolGet, NPUResponseToolGet>
{
  private static final QParameterNamed1<NPToolName> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The tool name."),
      Optional.empty(),
      NPToolName.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdToolGet(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "tool-get",
        new QConstant("Retrieve a tool."),
        Optional.empty()
      ),
      NPUCommandToolGet.class,
      NPUResponseToolGet.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(NAME);
  }

  @Override
  protected NPUCommandToolGet onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandToolGet(
      UUID.randomUUID(),
      context.parameterValue(NAME)
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseToolGet response)
    throws Exception
  {
    final var opt = response.description();
    if (opt.isPresent()) {
      final var data = opt.get();
      this.formatter().formatTool(data);
    }
  }
}
