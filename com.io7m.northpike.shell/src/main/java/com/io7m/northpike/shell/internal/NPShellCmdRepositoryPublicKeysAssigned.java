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
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPublicKeysAssigned;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryPublicKeysAssigned;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "repository-public-keys-assigned"
 */

public final class NPShellCmdRepositoryPublicKeysAssigned
  extends NPShellCmdAbstractCR<NPUCommandRepositoryPublicKeysAssigned, NPUResponseRepositoryPublicKeysAssigned>
{
  private static final QParameterNamed1<Integer> LIMIT =
    new QParameterNamed1<>(
      "--limit",
      List.of(),
      new QConstant("The maximum number of results per page."),
      Optional.of(Integer.valueOf(10)),
      Integer.class
    );

  private static final QParameterNamed1<NPRepositoryID> REPOSITORY_ID =
    new QParameterNamed1<>(
      "--repository",
      List.of(),
      new QConstant("The repository ID."),
      Optional.empty(),
      NPRepositoryID.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdRepositoryPublicKeysAssigned(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "repository-public-keys-assigned",
        new QConstant("List keys assigned to a repository."),
        Optional.empty()
      ),
      NPUCommandRepositoryPublicKeysAssigned.class,
      NPUResponseRepositoryPublicKeysAssigned.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      REPOSITORY_ID,
      LIMIT
    );
  }

  @Override
  protected NPUCommandRepositoryPublicKeysAssigned onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandRepositoryPublicKeysAssigned(
      UUID.randomUUID(),
      context.parameterValue(REPOSITORY_ID)
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseRepositoryPublicKeysAssigned response)
    throws Exception
  {
    this.formatter().formatFingerprints(response.keys());
  }
}
