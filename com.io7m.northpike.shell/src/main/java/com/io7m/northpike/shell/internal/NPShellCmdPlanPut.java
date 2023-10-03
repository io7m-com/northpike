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

import com.io7m.anethum.api.ParsingException;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "plan-put"
 */

public final class NPShellCmdPlanPut
  extends NPShellCmdAbstractCR<NPUCommandPlanPut, NPUResponseOK>
{
  private static final QParameterNamed1<Path> FILE =
    new QParameterNamed1<>(
      "--file",
      List.of(),
      new QConstant("The plan file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<NPPlanName> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The plan name."),
      Optional.empty(),
      NPPlanName.class
    );

  private static final QParameterNamed1<Long> VERSION =
    new QParameterNamed1<>(
      "--version",
      List.of(),
      new QConstant("The plan version."),
      Optional.empty(),
      Long.class
    );

  private static final QParameterNamed1<NPFormatName> FORMAT_NAME =
    new QParameterNamed1<>(
      "--format-name",
      List.of(),
      new QConstant("The plan description format."),
      Optional.empty(),
      NPFormatName.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdPlanPut(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "plan-put",
        new QConstant("Create/update a plan."),
        Optional.empty()
      ),
      NPUCommandPlanPut.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      FILE,
      NAME,
      VERSION,
      FORMAT_NAME
    );
  }

  @Override
  protected NPUCommandPlanPut onCreateCommand(
    final QCommandContextType context)
    throws IOException, ParsingException
  {
    final var file =
      context.parameterValue(FILE);
    final var data =
      Files.readString(file);

    final var toolExecution =
      new NPPlanDescriptionUnparsed(
        new NPPlanIdentifier(
          context.parameterValue(NAME),
          context.parameterValue(VERSION).longValue()
        ),
        context.parameterValue(FORMAT_NAME),
        data
      );

    return new NPUCommandPlanPut(
      UUID.randomUUID(),
      toolExecution
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseOK response)
  {

  }
}
