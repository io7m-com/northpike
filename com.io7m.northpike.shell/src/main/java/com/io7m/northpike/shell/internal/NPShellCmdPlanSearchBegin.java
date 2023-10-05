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

import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.plans.NPPlanSearchParameters;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponsePlanSearch;
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
 * "plan-search-begin"
 */

public final class NPShellCmdPlanSearchBegin
  extends NPShellCmdAbstractCR<NPUCommandPlanSearchBegin, NPUResponsePlanSearch>
{
  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  private static final QParameterNamed01<String> NAME_EQUALS =
    new QParameterNamed01<>(
      "--name-equal-to",
      List.of(),
      new QConstant("Filter plans by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_NEQUALS =
    new QParameterNamed01<>(
      "--name-not-equal-to",
      List.of(),
      new QConstant("Filter plans by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_SIMILAR =
    new QParameterNamed01<>(
      "--name-similar-to",
      List.of(),
      new QConstant("Filter plans by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_NOT_SIMILAR =
    new QParameterNamed01<>(
      "--name-not-similar-to",
      List.of(),
      new QConstant("Filter plans by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> DESCRIPTION_EQUALS =
    new QParameterNamed01<>(
      "--description-equal-to",
      List.of(),
      new QConstant("Filter plans by description."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> DESCRIPTION_NEQUALS =
    new QParameterNamed01<>(
      "--description-not-equal-to",
      List.of(),
      new QConstant("Filter plans by description."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> DESCRIPTION_SIMILAR =
    new QParameterNamed01<>(
      "--description-similar-to",
      List.of(),
      new QConstant("Filter plans by description."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> DESCRIPTION_NOT_SIMILAR =
    new QParameterNamed01<>(
      "--description-not-similar-to",
      List.of(),
      new QConstant("Filter plans by description."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdPlanSearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "plan-search-begin",
        new QConstant("Begin searching for plans."),
        Optional.empty()
      ),
      NPUCommandPlanSearchBegin.class,
      NPUResponsePlanSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      LIMIT,
      NAME_EQUALS,
      NAME_NEQUALS,
      NAME_SIMILAR,
      NAME_NOT_SIMILAR,
      DESCRIPTION_EQUALS,
      DESCRIPTION_NEQUALS,
      DESCRIPTION_SIMILAR,
      DESCRIPTION_NOT_SIMILAR
    );
  }

  @Override
  protected NPUCommandPlanSearchBegin onCreateCommand(
    final QCommandContextType context)
  {
    final var nameEquals =
      context.parameterValue(NAME_EQUALS)
        .map(NPComparisonFuzzyType.IsEqualTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var nameNequals =
      context.parameterValue(NAME_NEQUALS)
        .map(NPComparisonFuzzyType.IsNotEqualTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var nameSimilar =
      context.parameterValue(NAME_SIMILAR)
        .map(NPComparisonFuzzyType.IsSimilarTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var nameNotSimilar =
      context.parameterValue(NAME_NOT_SIMILAR)
        .map(NPComparisonFuzzyType.IsNotSimilarTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var descriptionEquals =
      context.parameterValue(DESCRIPTION_EQUALS)
        .map(NPComparisonFuzzyType.IsEqualTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var descriptionNequals =
      context.parameterValue(DESCRIPTION_NEQUALS)
        .map(NPComparisonFuzzyType.IsNotEqualTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var descriptionSimilar =
      context.parameterValue(DESCRIPTION_SIMILAR)
        .map(NPComparisonFuzzyType.IsSimilarTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var descriptionNotSimilar =
      context.parameterValue(DESCRIPTION_NOT_SIMILAR)
        .map(NPComparisonFuzzyType.IsNotSimilarTo::new)
        .map(x -> (NPComparisonFuzzyType<String>) x);

    final var nameMatch =
      nameEquals
        .or(() -> nameNequals)
        .or(() -> nameSimilar)
        .or(() -> nameNotSimilar)
        .orElse(new NPComparisonFuzzyType.Anything<>());

    final var descriptionMatch =
      descriptionEquals
        .or(() -> descriptionNequals)
        .or(() -> descriptionSimilar)
        .or(() -> descriptionNotSimilar)
        .orElse(new NPComparisonFuzzyType.Anything<>());

    final var toolExecutionMatch =
      new NPComparisonSetType.Anything<NPToolExecutionIdentifier>();

    final var parameters =
      new NPPlanSearchParameters(
        nameMatch,
        descriptionMatch,
        toolExecutionMatch,
        context.parameterValue(LIMIT).longValue()
      );

    return new NPUCommandPlanSearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponsePlanSearch response)
    throws Exception
  {
    this.formatter().formatPlanSummaries(response.results());
  }
}
