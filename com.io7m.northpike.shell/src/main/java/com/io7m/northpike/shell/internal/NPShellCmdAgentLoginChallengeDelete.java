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

import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeDelete;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

/**
 * "agent-login-challenge-delete"
 */

public final class NPShellCmdAgentLoginChallengeDelete
  extends NPShellCmdAbstractCR<NPUCommandAgentLoginChallengeDelete, NPUResponseOK>
{
  private static final QParameterNamed1<UUID> ID =
    new QParameterNamed1<>(
      "--id",
      List.of(),
      new QConstant("The ID of the login challenge record."),
      Optional.empty(),
      UUID.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAgentLoginChallengeDelete(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "agent-login-challenge-delete",
        new QConstant("Begin searching for agent login challenge records."),
        Optional.empty()
      ),
      NPUCommandAgentLoginChallengeDelete.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      ID
    );
  }

  @Override
  protected NPUCommandAgentLoginChallengeDelete onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandAgentLoginChallengeDelete(
      UUID.randomUUID(),
      Set.of(context.parameterValue(ID))
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseOK response)
    throws Exception
  {

  }
}
