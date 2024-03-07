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

import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.plans.NPPlanToolExecutionCompilerType;
import com.io7m.northpike.plans.variables.NPPlanVariableBoolean;
import com.io7m.northpike.plans.variables.NPPlanVariableInteger;
import com.io7m.northpike.plans.variables.NPPlanVariableString;
import com.io7m.northpike.plans.variables.NPPlanVariableStringSet;
import com.io7m.northpike.plans.variables.NPPlanVariableType;
import com.io7m.northpike.plans.variables.NPPlanVariables;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.api.NPTEvaluationResult;
import com.io7m.northpike.toolexec.api.NPTEvaluationServiceType;
import com.io7m.northpike.toolexec.program.api.NPTPVariableBoolean;
import com.io7m.northpike.toolexec.program.api.NPTPVariableInteger;
import com.io7m.northpike.toolexec.program.api.NPTPVariableString;
import com.io7m.northpike.toolexec.program.api.NPTPVariableStringSet;
import com.io7m.northpike.toolexec.program.api.NPTPVariableType;

import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.TOOL_EXECUTION;
import static com.io7m.northpike.strings.NPStringConstants.TOOL_EXECUTION_VERSION;

/**
 * A compiler for tool executions.
 */

public final class NPAssignmentToolExecutionCompiler
  implements NPPlanToolExecutionCompilerType
{
  private final NPStrings strings;
  private final NPDatabaseQueriesToolsType.GetExecutionDescriptionType toolGet;
  private final NPTEvaluationServiceType evaluationService;

  /**
   * A compiler for tool executions.
   *
   * @param inStrings    The strings
   * @param inEvaluation A tool execution evaluation service
   * @param inToolGet    A function to retrieve execution descriptions
   */

  public NPAssignmentToolExecutionCompiler(
    final NPStrings inStrings,
    final NPTEvaluationServiceType inEvaluation,
    final NPDatabaseQueriesToolsType.GetExecutionDescriptionType inToolGet)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.evaluationService =
      Objects.requireNonNull(inEvaluation, "inEvaluation");
    this.toolGet =
      Objects.requireNonNull(inToolGet, "toolGet");
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
  public NPTEvaluationResult toolCompile(
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
        .map(NPAssignmentToolExecutionCompiler::toVariable)
        .toList();

    final var storedExec =
      this.toolGet.execute(execution)
        .orElseThrow(() -> this.errorToolExecNonexistent(execution));

    final var evaluable =
      this.evaluationService.create(
        storedExec.format(),
        txVariables,
        storedExec.text()
      );

    return evaluable.execute();
  }

  private static NPTPVariableType toVariable(
    final NPPlanVariableType variable)
  {
    return switch (variable) {
      case final NPPlanVariableBoolean bool -> {
        yield new NPTPVariableBoolean(bool.name(), bool.value());
      }
      case final NPPlanVariableInteger integer -> {
        yield new NPTPVariableInteger(
          integer.name(), BigInteger.valueOf(integer.value()));
      }
      case final NPPlanVariableString string -> {
        yield new NPTPVariableString(string.name(), string.value());
      }
      case final NPPlanVariableStringSet stringSet -> {
        yield new NPTPVariableStringSet(stringSet.name(), stringSet.value());
      }
    };
  }
}
