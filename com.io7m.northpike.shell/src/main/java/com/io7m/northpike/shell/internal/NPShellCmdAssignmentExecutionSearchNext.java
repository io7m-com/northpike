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

import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionSearchNext;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionSearch;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "assignment-execution-search-next"
 */

public final class NPShellCmdAssignmentExecutionSearchNext
  extends NPShellCmdAbstractCR<
  NPUCommandAssignmentExecutionSearchNext, NPUResponseAssignmentExecutionSearch>
{
  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAssignmentExecutionSearchNext(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "assignment-execution-search-next",
        new QConstant("Go to the next page of assignment executions."),
        Optional.empty()
      ),
      NPUCommandAssignmentExecutionSearchNext.class,
      NPUResponseAssignmentExecutionSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of();
  }

  @Override
  protected NPUCommandAssignmentExecutionSearchNext onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandAssignmentExecutionSearchNext(UUID.randomUUID());
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseAssignmentExecutionSearch response)
    throws Exception
  {
    this.formatter().formatAssignmentExecutions(response.results());
  }
}
