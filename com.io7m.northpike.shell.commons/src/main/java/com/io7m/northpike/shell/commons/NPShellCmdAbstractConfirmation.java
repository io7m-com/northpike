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


package com.io7m.northpike.shell.commons;

import com.io7m.northpike.strings.NPStrings;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QParameterPositional;
import com.io7m.quarrel.core.QParametersPositionalType;
import com.io7m.quarrel.core.QParametersPositionalTyped;
import com.io7m.quarrel.core.QStringType;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.UUID;

import static com.io7m.northpike.strings.NPStringConstants.SHELL_CONFIRMATION_MISSING;

/**
 * An abstract command that requires user confirmation.
 */

public abstract class NPShellCmdAbstractConfirmation
  extends NPShellCmdAbstract
{
  private static final QParameterPositional<UUID> CONFIRMATION_ID =
    new QParameterPositional<>(
      "confirmation-id",
      new QStringType.QConstant("The confirmation ID"),
      UUID.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   * @param metadata   The metadata
   */

  protected NPShellCmdAbstractConfirmation(
    final RPServiceDirectoryType inServices,
    final QCommandMetadata metadata)
  {
    super(inServices, metadata);
  }

  @Override
  public final List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of();
  }

  @Override
  public final QParametersPositionalType onListPositionalParameters()
  {
    return new QParametersPositionalTyped(
      List.of(CONFIRMATION_ID)
    );
  }

  @Override
  public final QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var services =
      this.services();
    final var strings =
      services.requireService(NPStrings.class);
    final var confirmService =
      services.requireService(NPShellConfirmationServiceType.class);

    try {
      confirmService.confirm(context.parameterValue(CONFIRMATION_ID));
    } catch (final NPShellConfirmationMissing e) {
      context.output().println(strings.format(SHELL_CONFIRMATION_MISSING));
      return QCommandStatus.FAILURE;
    }

    return QCommandStatus.SUCCESS;
  }
}
