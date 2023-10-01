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

import com.io7m.northpike.model.NPAgentLabel;
import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "agent-label-put"
 */

public final class NPShellCmdAgentLabelPut
  extends NPShellCmdAbstractCR<NPUCommandAgentLabelPut, NPUResponseOK>
{
  private static final QParameterNamed1<NPAgentLabelName> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The agent label name."),
      Optional.empty(),
      NPAgentLabelName.class
    );

  private static final QParameterNamed1<String> DESCRIPTION =
    new QParameterNamed1<>(
      "--description",
      List.of(),
      new QConstant("The agent label description."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentLabelPut(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-label-put",
        new QConstant("Create/update an agent label."),
        Optional.empty()
      ),
      NPUCommandAgentLabelPut.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(NAME, DESCRIPTION);
  }

  @Override
  protected NPUCommandAgentLabelPut onCreateCommand(
    final QCommandContextType context)
    throws IOException
  {
    return new NPUCommandAgentLabelPut(
      UUID.randomUUID(),
      new NPAgentLabel(
        context.parameterValue(NAME),
        context.parameterValue(DESCRIPTION)
      )
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseOK response)
  {

  }
}
