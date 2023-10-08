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

import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignmentSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonExactType;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentSearch;
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
 * "assignment-search-begin"
 */

public final class NPShellCmdAssignmentSearchBegin
  extends NPShellCmdAbstractCR<NPUCommandAssignmentSearchBegin, NPUResponseAssignmentSearch>
{
  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  private static final QParameterNamed01<NPRepositoryID> REPOS_EQUALS =
    new QParameterNamed01<>(
      "--repository-equal-to",
      List.of(),
      new QConstant("Filter assignments by repository."),
      Optional.empty(),
      NPRepositoryID.class
    );

  private static final QParameterNamed01<NPRepositoryID> REPOS_NEQUALS =
    new QParameterNamed01<>(
      "--repository-not-equal-to",
      List.of(),
      new QConstant("Filter assignments by repository."),
      Optional.empty(),
      NPRepositoryID.class
    );

  private static final QParameterNamed01<NPPlanIdentifier> PLAN_EQUALS =
    new QParameterNamed01<>(
      "--plan-equal-to",
      List.of(),
      new QConstant("Filter assignments by plan."),
      Optional.empty(),
      NPPlanIdentifier.class
    );

  private static final QParameterNamed01<NPPlanIdentifier> PLAN_NEQUALS =
    new QParameterNamed01<>(
      "--plan-not-equal-to",
      List.of(),
      new QConstant("Filter assignments by plan."),
      Optional.empty(),
      NPPlanIdentifier.class
    );

  private static final QParameterNamed01<String> NAME_EQUALS =
    new QParameterNamed01<>(
      "--name-equal-to",
      List.of(),
      new QConstant("Filter assignments by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_NEQUALS =
    new QParameterNamed01<>(
      "--name-not-equal-to",
      List.of(),
      new QConstant("Filter assignments by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_SIMILAR =
    new QParameterNamed01<>(
      "--name-similar-to",
      List.of(),
      new QConstant("Filter assignments by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_NOT_SIMILAR =
    new QParameterNamed01<>(
      "--name-not-similar-to",
      List.of(),
      new QConstant("Filter assignments by name."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAssignmentSearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "assignment-search-begin",
        new QConstant("Begin searching for assignments."),
        Optional.empty()
      ),
      NPUCommandAssignmentSearchBegin.class,
      NPUResponseAssignmentSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      LIMIT,
      REPOS_EQUALS,
      REPOS_NEQUALS,
      PLAN_EQUALS,
      PLAN_NEQUALS,
      NAME_EQUALS,
      NAME_NEQUALS,
      NAME_SIMILAR,
      NAME_NOT_SIMILAR
    );
  }

  @Override
  protected NPUCommandAssignmentSearchBegin onCreateCommand(
    final QCommandContextType context)
  {
    final var repositoryEquals =
      context.parameterValue(REPOS_EQUALS);
    final var repositoryNequals =
      context.parameterValue(REPOS_NEQUALS);
    final var repositoryMatch =
      repositoryEquals.map(NPComparisonExactType.IsEqualTo::new)
        .map(x -> (NPComparisonExactType<NPRepositoryID>) x)
        .or(() -> repositoryNequals.map(NPComparisonExactType.IsNotEqualTo::new))
        .orElse(new NPComparisonExactType.Anything<>());

    final var planEquals =
      context.parameterValue(PLAN_EQUALS);
    final var planNequals =
      context.parameterValue(PLAN_NEQUALS);
    final var planMatch =
      planEquals.map(NPComparisonExactType.IsEqualTo::new)
        .map(x -> (NPComparisonExactType<NPPlanIdentifier>) x)
        .or(() -> planNequals.map(NPComparisonExactType.IsNotEqualTo::new))
        .orElse(new NPComparisonExactType.Anything<>());

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
    final var nameMatch =
      nameEquals
        .or(() -> nameNequals)
        .or(() -> nameSimilar)
        .or(() -> nameNotSimilar)
        .orElse(new NPComparisonFuzzyType.Anything<>());

    final var parameters =
      new NPAssignmentSearchParameters(
        repositoryMatch,
        planMatch,
        nameMatch,
        context.parameterValue(LIMIT)
          .longValue()
      );

    return new NPUCommandAssignmentSearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseAssignmentSearch response)
    throws Exception
  {
    this.formatter().formatAssignments(response.results());
  }
}
