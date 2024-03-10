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

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.preferences.api.NPPreferences;
import com.io7m.northpike.shell.commons.NPShellCmdAbstract;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "bookmark-remove"
 */

public final class NPShellCmdBookmarkRemove
  extends NPShellCmdAbstract
{
  private static final QParameterNamed1<String> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The name of the bookmark."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The shell context
   */

  public NPShellCmdBookmarkRemove(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "bookmark-remove",
        new QConstant("Remove a server bookmark."),
        Optional.empty()
      ));
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      NAME
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var name =
      context.parameterValue(NAME);

    this.preferences().preferences()
      .serverBookmarks()
      .stream()
      .filter(b -> Objects.equals(b.name(), name))
      .findFirst()
      .orElseThrow(() -> {
        return new NPException(
          "No such bookmark.",
          errorNonexistent(),
          Map.of(),
          Optional.empty()
        );
      });

    final var bookmarksMutable =
      new ArrayList<>(this.preferences().preferences().serverBookmarks());

    bookmarksMutable.removeIf(b -> Objects.equals(b.name(), name));

    this.preferences().update(oldPreferences -> {
      return new NPPreferences(
        oldPreferences.debuggingEnabled(),
        List.copyOf(bookmarksMutable),
        oldPreferences.recentFiles()
      );
    });
    return SUCCESS;
  }
}
