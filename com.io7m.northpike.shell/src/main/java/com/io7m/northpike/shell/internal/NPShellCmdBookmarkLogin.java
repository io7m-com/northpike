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

import com.io7m.idstore.model.IdName;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.preferences.api.NPPreferenceServerBookmark;
import com.io7m.northpike.preferences.api.NPPreferenceServerUsernamePassword;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.net.InetSocketAddress;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "bookmark-login"
 */

public final class NPShellCmdBookmarkLogin
  extends NPShellCmdAbstractU
{
  private static final QParameterNamed01<String> NAME =
    new QParameterNamed01<>(
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

  public NPShellCmdBookmarkLogin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "bookmark-login",
        new QConstant("Log in using a bookmark."),
        Optional.empty()
      ));
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(NAME);
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var bookmarkNameOpt =
      context.parameterValue(NAME);

    final NPPreferenceServerBookmark bookmark;
    if (bookmarkNameOpt.isPresent()) {
      final var bookmarkName = bookmarkNameOpt.get();
      bookmark = this.preferences().preferences()
        .serverBookmarks()
        .stream()
        .filter(b -> Objects.equals(b.name(), bookmarkName))
        .findFirst()
        .orElseThrow(NPShellCmdBookmarkLogin::noSuchBookmark);
    } else {
      bookmark = this.preferences().preferences()
        .serverBookmarks()
        .stream()
        .findFirst()
        .orElseThrow(NPShellCmdBookmarkLogin::noSuchBookmark);
    }

    this.client()
      .login(
        InetSocketAddress.createUnresolved(bookmark.host(), bookmark.port()),
        bookmark.tlsConfiguration(),
        userNameOf(bookmark),
        passwordOf(bookmark)
      );

    return SUCCESS;
  }

  private static NPException noSuchBookmark()
  {
    return new NPException(
      "No such bookmark.",
      errorNonexistent(),
      Map.of(),
      Optional.empty()
    );
  }

  private static IdName userNameOf(
    final NPPreferenceServerBookmark bookmark)
  {
    return switch (bookmark.credentials()) {
      case final NPPreferenceServerUsernamePassword c ->
        new IdName(c.username());
    };
  }

  private static String passwordOf(
    final NPPreferenceServerBookmark bookmark)
  {
    return switch (bookmark.credentials()) {
      case final NPPreferenceServerUsernamePassword c ->
        c.password();
    };
  }
}
