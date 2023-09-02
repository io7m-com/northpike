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


package com.io7m.northpike.server.internal.assignments;

import com.io7m.anethum.api.ParsingException;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.plans.NPPlanToolExecutionCompilerType;
import com.io7m.northpike.plans.variables.NPPlanVariableBoolean;
import com.io7m.northpike.plans.variables.NPPlanVariableNumeric;
import com.io7m.northpike.plans.variables.NPPlanVariableString;
import com.io7m.northpike.plans.variables.NPPlanVariableStringSet;
import com.io7m.northpike.plans.variables.NPPlanVariableType;
import com.io7m.northpike.plans.variables.NPPlanVariables;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;
import com.io7m.northpike.toolexec.checker.NPTXChecker;
import com.io7m.northpike.toolexec.checker.NPTXCheckerException;
import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;
import com.io7m.northpike.toolexec.model.NPTXDescription;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableNumeric;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableString;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableStringSet;
import com.io7m.northpike.toolexec.model.NPTXPlanVariableType;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URI;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Stream;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_NUMBERED;
import static com.io7m.northpike.strings.NPStringConstants.LOCATION_NUMBERED;
import static com.io7m.northpike.strings.NPStringConstants.TOOL_EXECUTION;
import static com.io7m.northpike.strings.NPStringConstants.TOOL_EXECUTION_FORMAT;
import static com.io7m.northpike.strings.NPStringConstants.TOOL_EXECUTION_VERSION;
import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * A compiler for tool executions.
 */

public final class NPAssignmentToolExecutionCompiler
  implements NPPlanToolExecutionCompilerType
{
  private final NPStrings strings;
  private final Set<NPTXParserFactoryType> toolExecParserFactories;
  private final NPDatabaseQueriesToolsType.GetExecutionDescriptionType toolGet;

  /**
   * A compiler for tool executions.
   *
   * @param inStrings                 The strings
   * @param inToolExecParserFactories A set of parser factories
   * @param inToolGet                 A function to retrieve execution descriptions
   */

  public NPAssignmentToolExecutionCompiler(
    final NPStrings inStrings,
    final Set<NPTXParserFactoryType> inToolExecParserFactories,
    final NPDatabaseQueriesToolsType.GetExecutionDescriptionType inToolGet)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.toolExecParserFactories =
      Objects.requireNonNull(
        inToolExecParserFactories,
        "toolExecParserFactories");
    this.toolGet =
      Objects.requireNonNull(inToolGet, "toolGet");
  }

  private NPTXDescription openParse(
    final NPToolExecutionIdentifier execution)
    throws NPException
  {
    final var storedExec =
      this.toolGet.execute(execution)
        .orElseThrow(() -> this.errorToolExecNonexistent(execution));

    for (final var parserFactory : this.toolExecParserFactories) {
      if (parserFactory.formats().contains(storedExec.format())) {
        final var textBytes = storedExec.text().getBytes(UTF_8);
        try (var textStream = new ByteArrayInputStream(textBytes)) {
          return parserFactory.parse(URI.create("urn:input"), textStream);
        } catch (final IOException e) {
          throw NPServerExceptions.errorIO(this.strings, e);
        } catch (final ParsingException e) {
          throw this.errorParse(e);
        }
      }
    }

    throw this.errorToolExecFormatUnsupported(storedExec);
  }

  private NPException errorParse(
    final ParsingException e)
    throws NPException
  {
    final var errors = new TreeMap<String, String>();

    final var status = e.statusValues();

    for (int index = 0; index < status.size(); ++index) {
      final var x = status.get(index);
      errors.put(
        this.strings.format(ERROR_NUMBERED, Integer.valueOf(index)),
        this.strings.format(x.message())
      );
      errors.put(
        this.strings.format(LOCATION_NUMBERED, Integer.valueOf(index)),
        this.strings.format(Integer.toUnsignedString(x.lexical().line()))
      );
    }

    throw new NPException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorParse(),
      Map.copyOf(errors),
      Optional.empty()
    );
  }

  private NPServerException errorToolExecFormatUnsupported(
    final NPToolExecutionDescription description)
  {
    final var identifier = description.identifier();
    return new NPServerException(
      this.strings.format(NPStringConstants.ERROR_NONEXISTENT),
      NPStandardErrorCodes.errorUnsupported(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(TOOL_EXECUTION),
          identifier.name().toString()
        ),
        Map.entry(
          this.strings.format(TOOL_EXECUTION_VERSION),
          Long.toUnsignedString(identifier.version())
        ),
        Map.entry(
          this.strings.format(TOOL_EXECUTION_FORMAT),
          description.format().toString()
        )
      ),
      Optional.empty()
    );
  }

  private NPServerException errorToolExecNonexistent(
    final NPToolExecutionIdentifier exec)
  {
    return new NPServerException(
      this.strings.format(NPStringConstants.ERROR_NONEXISTENT),
      NPStandardErrorCodes.errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(TOOL_EXECUTION),
          exec.name().toString()
        ),
        Map.entry(
          this.strings.format(TOOL_EXECUTION_VERSION),
          Long.toUnsignedString(exec.version())
        )
      ),
      Optional.empty()
    );
  }

  @Override
  public NPTXTypeChecked toolCompile(
    final NPToolExecutionIdentifier execution,
    final NPPlanVariables planVariables)
    throws NPException
  {
    Objects.requireNonNull(execution, "execution");
    Objects.requireNonNull(planVariables, "planVariables");

    final var txVariables =
      planVariables.variables()
        .values()
        .stream()
        .map(NPAssignmentToolExecutionCompiler::toTxVariable)
        .toList();

    final var parsed =
      this.openParse(execution);

    try {
      return NPTXChecker.checkDescription(
        NPTXPlanVariables.ofList(txVariables),
        parsed
      );
    } catch (final NPTXCheckerException e) {
      throw this.errorCheckerException(e);
    }
  }

  private NPException errorCheckerException(
    final NPTXCheckerException e)
    throws NPException
  {
    final var errors = new TreeMap<String, String>();

    final var linearized =
      linearize(e)
        .toList();

    for (int index = 0; index < linearized.size(); ++index) {
      final var x = linearized.get(index);
      errors.put(
        this.strings.format(ERROR_NUMBERED, Integer.valueOf(index)),
        this.strings.format(x.message())
      );
      errors.put(
        this.strings.format(LOCATION_NUMBERED, Integer.valueOf(index)),
        this.strings.format(Integer.toUnsignedString(x.lexical().line()))
      );
    }

    throw new NPException(
      this.strings.format(e.message()),
      e,
      NPStandardErrorCodes.errorTypeCheckFailed(),
      Map.copyOf(errors),
      Optional.empty()
    );
  }

  private static Stream<NPTXCheckerException> linearize(
    final NPTXCheckerException e)
  {
    return Stream.concat(
      Stream.of(e),
      Stream.of(e.getSuppressed())
        .filter(x -> x instanceof NPTXCheckerException)
        .map(x -> (NPTXCheckerException) x)
        .flatMap(NPAssignmentToolExecutionCompiler::linearize)
    );
  }

  private static NPTXPlanVariableType toTxVariable(
    final NPPlanVariableType v)
  {
    if (v instanceof final NPPlanVariableString vv) {
      return new NPTXPlanVariableString(vv.name(), vv.value());
    }
    if (v instanceof final NPPlanVariableBoolean vv) {
      return new NPTXPlanVariableBoolean(vv.name(), vv.value());
    }
    if (v instanceof final NPPlanVariableStringSet vv) {
      return new NPTXPlanVariableStringSet(vv.name(), vv.value());
    }
    if (v instanceof final NPPlanVariableNumeric vv) {
      return new NPTXPlanVariableNumeric(vv.name(), vv.value());
    }

    throw new IllegalStateException(
      "Unrecognized variable type: %s".formatted(v)
    );
  }
}
