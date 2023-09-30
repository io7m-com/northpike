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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPRepositoryCredentialsType;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.net.URI;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.model.NPRepositoryCredentialsNone.CREDENTIALS_NONE;
import static com.io7m.northpike.model.NPRepositorySigningPolicy.REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS;

/**
 * "repository-put"
 */

public final class NPShellCmdRepositoryPut
  extends NPShellCmdAbstractCR<NPUCommandRepositoryPut, NPUResponseOK>
{
  private static final QParameterNamed1<NPRepositoryID> REPOSITORY_ID =
    new QParameterNamed1<>(
      "--id",
      List.of(),
      new QConstant("The repository ID."),
      Optional.empty(),
      NPRepositoryID.class
    );

  private static final QParameterNamed1<RDottedName> REPOSITORY_PROVIDER =
    new QParameterNamed1<>(
      "--provider",
      List.of(),
      new QConstant("The repository SCM provider."),
      Optional.empty(),
      RDottedName.class
    );

  private static final QParameterNamed1<URI> REPOSITORY_URI =
    new QParameterNamed1<>(
      "--uri",
      List.of(),
      new QConstant("The repository URI."),
      Optional.empty(),
      URI.class
    );

  private static final QParameterNamed1<NPRepositoryCredentialsType> REPOSITORY_CREDENTIALS =
    new QParameterNamed1<>(
      "--credentials",
      List.of(),
      new QConstant("The repository credentials."),
      Optional.of(CREDENTIALS_NONE),
      NPRepositoryCredentialsType.class
    );

  private static final QParameterNamed1<NPRepositorySigningPolicy> REPOSITORY_SIGNING_POLICY =
    new QParameterNamed1<>(
      "--signing-policy",
      List.of(),
      new QConstant("The repository signing policy."),
      Optional.of(REQUIRE_COMMITS_SIGNED_WITH_SPECIFIC_KEYS),
      NPRepositorySigningPolicy.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdRepositoryPut(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "repository-put",
        new QConstant("Create/update a repository."),
        Optional.empty()
      ),
      NPUCommandRepositoryPut.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      REPOSITORY_CREDENTIALS,
      REPOSITORY_ID,
      REPOSITORY_PROVIDER,
      REPOSITORY_SIGNING_POLICY,
      REPOSITORY_URI
    );
  }

  @Override
  protected NPUCommandRepositoryPut onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandRepositoryPut(
      UUID.randomUUID(),
      new NPRepositoryDescription(
        context.parameterValue(REPOSITORY_PROVIDER),
        context.parameterValue(REPOSITORY_ID),
        context.parameterValue(REPOSITORY_URI),
        context.parameterValue(REPOSITORY_CREDENTIALS),
        context.parameterValue(REPOSITORY_SIGNING_POLICY)
      )
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseOK response)
  {

  }
}
