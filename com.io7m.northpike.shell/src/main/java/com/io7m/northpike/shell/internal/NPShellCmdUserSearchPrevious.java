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

import com.io7m.northpike.protocol.user.NPUCommandUserSearchPrevious;
import com.io7m.northpike.protocol.user.NPUResponseUserSearch;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "user-search-previous"
 */

public final class NPShellCmdUserSearchPrevious
  extends NPShellCmdAbstractCR<NPUCommandUserSearchPrevious, NPUResponseUserSearch>
{
  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdUserSearchPrevious(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "user-search-previous",
        new QConstant("Go to the previous page of users."),
        Optional.empty()
      ),
      NPUCommandUserSearchPrevious.class,
      NPUResponseUserSearch.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of();
  }

  @Override
  protected NPUCommandUserSearchPrevious onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandUserSearchPrevious(UUID.randomUUID());
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
