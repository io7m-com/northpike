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

import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionSearch;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "tool-execution-search-begin"
 */

public final class NPShellCmdToolExecutionDescriptionSearchBegin
  extends NPShellCmdAbstractCR<NPUCommandToolExecutionDescriptionSearchBegin, NPUResponseToolExecutionDescriptionSearch>
{
  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  private static final QParameterNamed01<NPToolName> TOOL_EQUALS =
    new QParameterNamed01<>(
      "--tool-equal-to",
      List.of(),
      new QConstant("Filter executions by tool."),
      Optional.empty(),
      NPToolName.class
    );

  private static final QParameterNamed01<NPToolName> TOOL_NEQUALS =
    new QParameterNamed01<>(
      "--tool-not-equal-to",
      List.of(),
      new QConstant("Filter executions by tool."),
      Optional.empty(),
      NPToolName.class
    );


  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdToolExecutionDescriptionSearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "tool-execution-search-begin",
        new QConstant("Begin searching for tool executions."),
        Optional.empty()
      ),
      NPUCommandToolExecutionDescriptionSearchBegin.class,
      NPUResponseToolExecutionDescriptionSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      LIMIT,
      TOOL_EQUALS,
      TOOL_NEQUALS
    );
  }

  @Override
  protected NPUCommandToolExecutionDescriptionSearchBegin onCreateCommand(
    final QCommandContextType context)
  {
    final var toolEquals =
      context.parameterValue(TOOL_EQUALS);
    final var toolNequals =
      context.parameterValue(TOOL_NEQUALS);
    final var toolMatch =
      toolEquals.map(NPComparisonExactType.IsEqualTo::new)
        .map(x -> (NPComparisonExactType<NPToolName>) x)
        .or(() -> toolNequals.map(NPComparisonExactType.IsNotEqualTo::new))
        .orElse(new NPComparisonExactType.Anything<>());

    final var parameters =
      new NPToolExecutionDescriptionSearchParameters(
        toolMatch,
        context.parameterValue(LIMIT).longValue()
      );

    return new NPUCommandToolExecutionDescriptionSearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseToolExecutionDescriptionSearch response)
    throws Exception
  {
    this.formatter().formatToolExecutionDescriptionSummaries(response.results());
  }
}
