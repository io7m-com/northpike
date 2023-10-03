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

import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import com.io7m.northpike.protocol.user.NPUCommandPlanDelete;
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
 * "plan-delete"
 */

public final class NPShellCmdPlanDelete
  extends NPShellCmdAbstractCR<NPUCommandPlanDelete, NPUResponseOK>
{
  private static final QParameterNamed1<NPPlanName> PLAN_NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The plan name."),
      Optional.empty(),
      NPPlanName.class
    );

  private static final QParameterNamed1<Long> PLAN_VERSION =
    new QParameterNamed1<>(
      "--version",
      List.of(),
      new QConstant("The plan version."),
      Optional.empty(),
      Long.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdPlanDelete(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "plan-delete",
        new QConstant("Delete plans."),
        Optional.empty()
      ),
      NPUCommandPlanDelete.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      PLAN_NAME,
      PLAN_VERSION
    );
  }

  @Override
  protected NPUCommandPlanDelete onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandPlanDelete(
      UUID.randomUUID(),
      Set.of(
        new NPPlanIdentifier(
          context.parameterValue(PLAN_NAME),
          context.parameterValue(PLAN_VERSION).longValue()
        )
      )
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
