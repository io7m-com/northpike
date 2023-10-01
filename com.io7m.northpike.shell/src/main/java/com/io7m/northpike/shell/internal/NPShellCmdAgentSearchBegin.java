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

import com.io7m.northpike.model.NPAgentLabelName;
import com.io7m.northpike.model.NPAgentLabelSet;
import com.io7m.northpike.model.NPAgentSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseAgentSearch;
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
 * "agent-search-begin"
 */

public final class NPShellCmdAgentSearchBegin
  extends NPShellCmdAbstractCR<NPUCommandAgentSearchBegin, NPUResponseAgentSearch>
{
  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  private static final QParameterNamed01<NPAgentLabelSet> LABELS_EQUALS =
    new QParameterNamed01<>(
      "--labels-equal-to",
      List.of(),
      new QConstant("Filter agents by labels."),
      Optional.empty(),
      NPAgentLabelSet.class
    );

  private static final QParameterNamed01<NPAgentLabelSet> LABELS_NEQUALS =
    new QParameterNamed01<>(
      "--labels-not-equal-to",
      List.of(),
      new QConstant("Filter agents by labels."),
      Optional.empty(),
      NPAgentLabelSet.class
    );

  private static final QParameterNamed01<NPAgentLabelSet> LABELS_SUBSET =
    new QParameterNamed01<>(
      "--labels-subset-of",
      List.of(),
      new QConstant("Filter agents by labels."),
      Optional.empty(),
      NPAgentLabelSet.class
    );

  private static final QParameterNamed01<NPAgentLabelSet> LABELS_SUPERSET =
    new QParameterNamed01<>(
      "--labels-superset-of",
      List.of(),
      new QConstant("Filter agents by labels."),
      Optional.empty(),
      NPAgentLabelSet.class
    );

  private static final QParameterNamed01<NPAgentLabelSet> LABELS_OVERLAPPING =
    new QParameterNamed01<>(
      "--labels-overlapping",
      List.of(),
      new QConstant("Filter agents by labels."),
      Optional.empty(),
      NPAgentLabelSet.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentSearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-search-begin",
        new QConstant("Begin searching for agents."),
        Optional.empty()
      ),
      NPUCommandAgentSearchBegin.class,
      NPUResponseAgentSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      LIMIT,
      LABELS_EQUALS,
      LABELS_NEQUALS,
      LABELS_SUBSET,
      LABELS_SUPERSET,
      LABELS_OVERLAPPING
    );
  }

  @Override
  protected NPUCommandAgentSearchBegin onCreateCommand(
    final QCommandContextType context)
  {
    final var labelsEquals =
      context.parameterValue(LABELS_EQUALS)
        .map(NPAgentLabelSet::labels)
        .map(NPComparisonSetType.IsEqualTo::new)
        .map(x -> (NPComparisonSetType<NPAgentLabelName>) x);

    final var labelsNequals =
      context.parameterValue(LABELS_NEQUALS)
        .map(NPAgentLabelSet::labels)
        .map(NPComparisonSetType.IsNotEqualTo::new)
        .map(x -> (NPComparisonSetType<NPAgentLabelName>) x);

    final var labelsSubset =
      context.parameterValue(LABELS_SUBSET)
        .map(NPAgentLabelSet::labels)
        .map(NPComparisonSetType.IsSubsetOf::new)
        .map(x -> (NPComparisonSetType<NPAgentLabelName>) x);

    final var labelsSuperset =
      context.parameterValue(LABELS_SUPERSET)
        .map(NPAgentLabelSet::labels)
        .map(NPComparisonSetType.IsSupersetOf::new)
        .map(x -> (NPComparisonSetType<NPAgentLabelName>) x);

    final var labelsOverlapping =
      context.parameterValue(LABELS_OVERLAPPING)
        .map(NPAgentLabelSet::labels)
        .map(NPComparisonSetType.IsOverlapping::new)
        .map(x -> (NPComparisonSetType<NPAgentLabelName>) x);

    final var labelsMatch =
      labelsEquals
        .or(() -> labelsNequals)
        .or(() -> labelsSubset)
        .or(() -> labelsSuperset)
        .or(() -> labelsOverlapping)
        .orElse(new NPComparisonSetType.Anything<>());

    final var parameters =
      new NPAgentSearchParameters(
        labelsMatch,
        context.parameterValue(LIMIT)
          .longValue()
      );

    return new NPUCommandAgentSearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseAgentSearch response)
    throws Exception
  {
    this.formatter().formatAgentSummaries(response.results());
  }
}
