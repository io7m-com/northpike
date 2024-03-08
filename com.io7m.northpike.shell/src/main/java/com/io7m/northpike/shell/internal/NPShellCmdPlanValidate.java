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
import com.io7m.northpike.protocol.user.NPUCommandPlanValidate;
import com.io7m.northpike.protocol.user.NPUResponsePlanValidate;
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

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * "plan-validate"
 */

public final class NPShellCmdPlanValidate
  extends NPShellCmdAbstractCR<
  NPUCommandPlanValidate,
  NPUResponsePlanValidate>
{
  private static final QParameterNamed1<Path> FILE =
    new QParameterNamed1<>(
      "--file",
      List.of(),
      new QConstant("The plan description file."),
      Optional.empty(),
      Path.class
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

  public NPShellCmdPlanValidate(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "plan-validate",
        new QConstant("Validate a plan description."),
        Optional.empty()
      ),
      NPUCommandPlanValidate.class,
      NPUResponsePlanValidate.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      FILE,
      FORMAT_NAME
    );
  }

  @Override
  protected NPUCommandPlanValidate onCreateCommand(
    final QCommandContextType context)
    throws ParsingException, IOException
  {
    final var text =
      Files.readString(context.parameterValue(FILE), UTF_8);

    final var description =
      new NPPlanDescriptionUnparsed(
        new NPPlanIdentifier(
          NPPlanName.of("com.northpike.example"),
          1L
        ),
        context.parameterValue(FORMAT_NAME),
        text
      );

    return new NPUCommandPlanValidate(
      UUID.randomUUID(),
      description
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponsePlanValidate response)
  {
    final var w = context.output();

    if (!response.isValid()) {
      w.println("Validation failed.");
    } else {
      w.println("Validation succeeded.");
    }

    w.println();

    for (final var error : response.compilationErrors()) {
      w.print(error.errorCode());
      w.print(":");
      w.print(error.message());
      w.println();
      for (final var entry : error.attributes().entrySet()) {
        w.println("  ");
        w.print(entry.getKey());
        w.print(":");
        w.print(entry.getValue());
        w.println();
      }
    }

    w.println();
    w.flush();
  }
}
