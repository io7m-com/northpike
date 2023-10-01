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

import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.model.NPUserSearchParameters;
import com.io7m.northpike.model.comparisons.NPComparisonFuzzyType;
import com.io7m.northpike.model.comparisons.NPComparisonSetType;
import com.io7m.northpike.model.security.NPRoleSet;
import com.io7m.northpike.protocol.user.NPUCommandUserSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseUserSearch;
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
 * "user-search-begin"
 */

public final class NPShellCmdUserSearchBegin
  extends NPShellCmdAbstractCR<NPUCommandUserSearchBegin, NPUResponseUserSearch>
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
      new QConstant("Filter users by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_NEQUALS =
    new QParameterNamed01<>(
      "--name-not-equal-to",
      List.of(),
      new QConstant("Filter users by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_SIMILAR =
    new QParameterNamed01<>(
      "--name-similar-to",
      List.of(),
      new QConstant("Filter users by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<String> NAME_NOT_SIMILAR =
    new QParameterNamed01<>(
      "--name-not-similar-to",
      List.of(),
      new QConstant("Filter users by name."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed01<NPRoleSet> ROLES_EQUALS =
    new QParameterNamed01<>(
      "--roles-equal-to",
      List.of(),
      new QConstant("Filter users by roles."),
      Optional.empty(),
      NPRoleSet.class
    );

  private static final QParameterNamed01<NPRoleSet> ROLES_NEQUALS =
    new QParameterNamed01<>(
      "--roles-not-equal-to",
      List.of(),
      new QConstant("Filter users by roles."),
      Optional.empty(),
      NPRoleSet.class
    );

  private static final QParameterNamed01<NPRoleSet> ROLES_SUBSET =
    new QParameterNamed01<>(
      "--roles-subset-of",
      List.of(),
      new QConstant("Filter users by roles."),
      Optional.empty(),
      NPRoleSet.class
    );

  private static final QParameterNamed01<NPRoleSet> ROLES_SUPERSET =
    new QParameterNamed01<>(
      "--roles-superset-of",
      List.of(),
      new QConstant("Filter users by roles."),
      Optional.empty(),
      NPRoleSet.class
    );

  private static final QParameterNamed01<NPRoleSet> ROLES_OVERLAPPING =
    new QParameterNamed01<>(
      "--roles-overlapping",
      List.of(),
      new QConstant("Filter users by roles."),
      Optional.empty(),
      NPRoleSet.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdUserSearchBegin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "user-search-begin",
        new QConstant("Begin searching for users."),
        Optional.empty()
      ),
      NPUCommandUserSearchBegin.class,
      NPUResponseUserSearch.class
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

      ROLES_EQUALS,
      ROLES_NEQUALS,
      ROLES_SUBSET,
      ROLES_SUPERSET,
      ROLES_OVERLAPPING
    );
  }

  @Override
  protected NPUCommandUserSearchBegin onCreateCommand(
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

    final var rolesEquals =
      context.parameterValue(ROLES_EQUALS)
        .map(NPRoleSet::roles)
        .map(NPComparisonSetType.IsEqualTo::new)
        .map(x -> (NPComparisonSetType<MRoleName>) x);

    final var rolesNequals =
      context.parameterValue(ROLES_NEQUALS)
        .map(NPRoleSet::roles)
        .map(NPComparisonSetType.IsNotEqualTo::new)
        .map(x -> (NPComparisonSetType<MRoleName>) x);

    final var rolesSubset =
      context.parameterValue(ROLES_SUBSET)
        .map(NPRoleSet::roles)
        .map(NPComparisonSetType.IsSubsetOf::new)
        .map(x -> (NPComparisonSetType<MRoleName>) x);

    final var rolesSuperset =
      context.parameterValue(ROLES_SUPERSET)
        .map(NPRoleSet::roles)
        .map(NPComparisonSetType.IsSupersetOf::new)
        .map(x -> (NPComparisonSetType<MRoleName>) x);

    final var rolesOverlapping =
      context.parameterValue(ROLES_OVERLAPPING)
        .map(NPRoleSet::roles)
        .map(NPComparisonSetType.IsOverlapping::new)
        .map(x -> (NPComparisonSetType<MRoleName>) x);

    final var nameMatch =
      nameEquals
        .or(() -> nameNequals)
        .or(() -> nameSimilar)
        .or(() -> nameNotSimilar)
        .orElse(new NPComparisonFuzzyType.Anything<>());

    final var rolesMatch =
      rolesEquals
        .or(() -> rolesNequals)
        .or(() -> rolesSubset)
        .or(() -> rolesSuperset)
        .or(() -> rolesOverlapping)
        .orElse(new NPComparisonSetType.Anything<>());

    final var parameters =
      new NPUserSearchParameters(
        nameMatch,
        rolesMatch,
        context.parameterValue(LIMIT).longValue()
      );

    return new NPUCommandUserSearchBegin(UUID.randomUUID(), parameters);
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseUserSearch response)
    throws Exception
  {
    this.formatter().formatUsers(response.results());
  }
}
