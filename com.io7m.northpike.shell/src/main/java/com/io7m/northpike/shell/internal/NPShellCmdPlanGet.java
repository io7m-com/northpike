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
import com.io7m.northpike.protocol.user.NPUCommandPlanGet;
import com.io7m.northpike.protocol.user.NPUResponsePlanGet;
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
 * "plan-get"
 */

public final class NPShellCmdPlanGet
  extends NPShellCmdAbstractCR<NPUCommandPlanGet, NPUResponsePlanGet>
{
  private static final QParameterNamed1<NPPlanName> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The plan name."),
      Optional.empty(),
      NPPlanName.class
    );

  private static final QParameterNamed1<Long> VERSION =
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

  public NPShellCmdPlanGet(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "plan-get",
        new QConstant("Retrieve a plan."),
        Optional.empty()
      ),
      NPUCommandPlanGet.class,
      NPUResponsePlanGet.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(NAME, VERSION);
  }

  @Override
  protected NPUCommandPlanGet onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandPlanGet(
      UUID.randomUUID(),
      new NPPlanIdentifier(
        context.parameterValue(NAME),
        context.parameterValue(VERSION).longValue()
      )
    );
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponsePlanGet response)
    throws Exception
  {
    final var opt = response.plan();
    if (opt.isPresent()) {
      final var data = opt.get();
      this.formatter().formatPlan(data);
    }
  }
}
