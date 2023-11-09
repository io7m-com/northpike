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

import com.io7m.northpike.shell.commons.NPShellCmdAbstract;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandHelpFormatting;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandTreeResolver;
import com.io7m.quarrel.core.QCommandTreeResolver.QResolutionOKCommand;
import com.io7m.quarrel.core.QCommandTreeResolver.QResolutionOKGroup;
import com.io7m.quarrel.core.QCommandTreeResolver.QResolutionRoot;
import com.io7m.quarrel.core.QException;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QParametersPositionalAny;
import com.io7m.quarrel.core.QParametersPositionalType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;

import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "help"
 */

public final class NPShellCmdHelp extends NPShellCmdAbstract
{
  /**
   * Construct a command.
   *
   * @param inServices The services
   */

  public NPShellCmdHelp(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "help",
        new QConstant("Display help for a given command."),
        Optional.empty()
      )
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of();
  }

  @Override
  public QParametersPositionalType onListPositionalParameters()
  {
    return new QParametersPositionalAny();
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws QException
  {
    final var resolution =
      QCommandTreeResolver.resolve(
        context.commandTree(),
        context.parametersPositionalRaw()
      );

    if (resolution instanceof QResolutionRoot) {
      QCommandHelpFormatting.formatCommand(
        context.valueConverters(),
        context,
        "northpike",
        context.output(),
        this
      );
      return SUCCESS;
    }

    if (resolution instanceof QResolutionOKCommand cmd) {
      QCommandHelpFormatting.formatCommand(
        context.valueConverters(),
        context,
        "northpike",
        context.output(),
        cmd.command()
      );
      return SUCCESS;
    }

    if (resolution instanceof QResolutionOKGroup group) {
      QCommandHelpFormatting.formatGroup(
        context.valueConverters(),
        context,
        "northpike",
        context.output(),
        group.target(),
        group.path()
      );
      return SUCCESS;
    }

    return SUCCESS;
  }
}
