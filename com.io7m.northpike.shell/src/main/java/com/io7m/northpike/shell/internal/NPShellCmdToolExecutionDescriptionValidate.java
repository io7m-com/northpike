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
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionValidate;
import com.io7m.northpike.toolexec.program.api.NPTPVariableBoolean;
import com.io7m.northpike.toolexec.program.api.NPTPVariableInteger;
import com.io7m.northpike.toolexec.program.api.NPTPVariableString;
import com.io7m.northpike.toolexec.program.api.NPTPVariableStringSet;
import com.io7m.northpike.toolexec.program.api.NPTPVariableType;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed0N;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * "tool-execution-validate"
 */

public final class NPShellCmdToolExecutionDescriptionValidate
  extends NPShellCmdAbstractCR<
  NPUCommandToolExecutionDescriptionValidate,
  NPUResponseToolExecutionDescriptionValidate>
{
  private static final QParameterNamed1<Path> FILE =
    new QParameterNamed1<>(
      "--file",
      List.of(),
      new QConstant("The tool execution description file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<NPFormatName> FORMAT_NAME =
    new QParameterNamed1<>(
      "--format-name",
      List.of(),
      new QConstant("The tool execution description format."),
      Optional.empty(),
      NPFormatName.class
    );

  private static final QParameterNamed0N<RDottedName> VARIABLE_BOOLEAN =
    new QParameterNamed0N<>(
      "--variable-boolean",
      List.of(),
      new QConstant("Declare a named boolean-typed plan variable."),
      List.of(),
      RDottedName.class
    );

  private static final QParameterNamed0N<RDottedName> VARIABLE_INTEGER =
    new QParameterNamed0N<>(
      "--variable-integer",
      List.of(),
      new QConstant("Declare a named integer-typed plan variable."),
      List.of(),
      RDottedName.class
    );

  private static final QParameterNamed0N<RDottedName> VARIABLE_STRING =
    new QParameterNamed0N<>(
      "--variable-string",
      List.of(),
      new QConstant("Declare a named string-typed plan variable."),
      List.of(),
      RDottedName.class
    );

  private static final QParameterNamed0N<RDottedName> VARIABLE_STRING_SET =
    new QParameterNamed0N<>(
      "--variable-string-set",
      List.of(),
      new QConstant("Declare a named string-set-typed plan variable."),
      List.of(),
      RDottedName.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdToolExecutionDescriptionValidate(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "tool-execution-validate",
        new QConstant("Validate a tool execution description."),
        Optional.empty()
      ),
      NPUCommandToolExecutionDescriptionValidate.class,
      NPUResponseToolExecutionDescriptionValidate.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      FILE,
      FORMAT_NAME,
      VARIABLE_BOOLEAN,
      VARIABLE_INTEGER,
      VARIABLE_STRING,
      VARIABLE_STRING_SET
    );
  }

  @Override
  protected NPUCommandToolExecutionDescriptionValidate onCreateCommand(
    final QCommandContextType context)
    throws ParsingException, IOException
  {
    final var variables =
      new ArrayList<NPTPVariableType>();

    for (final var x : context.parameterValues(VARIABLE_BOOLEAN)) {
      variables.add(new NPTPVariableBoolean(x, false));
    }
    for (final var x : context.parameterValues(VARIABLE_INTEGER)) {
      variables.add(new NPTPVariableInteger(x, BigInteger.valueOf(0L)));
    }
    for (final var x : context.parameterValues(VARIABLE_STRING)) {
      variables.add(new NPTPVariableString(x, ""));
    }
    for (final var x : context.parameterValues(VARIABLE_STRING_SET)) {
      variables.add(new NPTPVariableStringSet(x, Set.of()));
    }

    final var text =
      Files.readString(context.parameterValue(FILE), UTF_8);

    final var description =
      new NPToolExecutionDescription(
        new NPToolExecutionIdentifier(
          NPToolExecutionName.of("com.northpike.example"),
          1L
        ),
        NPToolName.of("com.northpike.example"),
        "",
        context.parameterValue(FORMAT_NAME),
        text
      );

    return new NPUCommandToolExecutionDescriptionValidate(
      UUID.randomUUID(),
      variables,
      description
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseToolExecutionDescriptionValidate response)
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
