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
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.SHELL_CONFIRMATION_REQUIRED;
import static com.io7m.northpike.strings.NPStringConstants.SHELL_CONFIRMATION_REQUIRED_ANSWER;
import static java.lang.Boolean.TRUE;

/**
 * An abstract command that requires user confirmation.
 */

public abstract class NPShellCmdAbstractConfirmationRequired
  extends NPShellCmdAbstract
{
  private static final QParameterNamed1<Boolean> ASK_FOR_CONFIRMATION =
    new QParameterNamed1<>(
      "--ask-for-confirmation",
      List.of(),
      new QStringType.QConstant(
        "Ask for confirmation before performing the operation."),
      Optional.of(TRUE),
      Boolean.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   * @param metadata   The metadata
   */

  protected NPShellCmdAbstractConfirmationRequired(
    final RPServiceDirectoryType inServices,
    final QCommandMetadata metadata)
  {
    super(inServices, metadata);
  }

  @Override
  public final List<QParameterNamedType<?>> onListNamedParameters()
  {
    final var arguments = new ArrayList<QParameterNamedType<?>>();
    arguments.add(ASK_FOR_CONFIRMATION);
    arguments.addAll(this.onListNamedParametersConfirmed());
    return List.copyOf(arguments);
  }

  protected abstract Collection<? extends QParameterNamedType<?>>
  onListNamedParametersConfirmed();

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

    final var request =
      this.onRequireConfirmation(context);

    if (context.<Boolean>parameterValue(ASK_FOR_CONFIRMATION).booleanValue()) {
      final var requirement = confirmService.register(request);
      final var writer = context.output();
      writer.println(strings.format(SHELL_CONFIRMATION_REQUIRED));
      writer.println();
      writer.println(strings.format(SHELL_CONFIRMATION_REQUIRED_ANSWER));
      writer.println();

      writer.print("  ");
      writer.print(request.command());
      writer.print(" ");
      writer.print(requirement.confirmation());
      writer.println();
      writer.println();

      return QCommandStatus.SUCCESS;
    }

    request.operation().execute();
    return QCommandStatus.SUCCESS;
  }

  protected abstract NPShellConfirmationRequest onRequireConfirmation(
    QCommandContextType context);

}
