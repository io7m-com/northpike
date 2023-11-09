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
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.net.InetSocketAddress;
import java.util.List;
import java.util.Optional;

import static com.io7m.northpike.model.tls.NPTLSDisabled.TLS_DISABLED;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * "login"
 */

public final class NPShellCmdLogin extends NPShellCmdAbstractU
{
  private static final QParameterNamed1<String> SERVER =
    new QParameterNamed1<>(
      "--server",
      List.of(),
      new QConstant(
        "The server hostname."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed1<Integer> PORT =
    new QParameterNamed1<>(
      "--port",
      List.of(),
      new QConstant(
        "The server port."),
      Optional.empty(),
      Integer.class
    );

  private static final QParameterNamed1<String> USERNAME =
    new QParameterNamed1<>(
      "--user",
      List.of(),
      new QConstant(
        "The username."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed1<String> PASSWORD =
    new QParameterNamed1<>(
      "--password",
      List.of(),
      new QConstant(
        "The password."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The services
   */

  public NPShellCmdLogin(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "login",
        new QConstant("Log in."),
        Optional.empty()
      )
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      SERVER,
      PORT,
      USERNAME,
      PASSWORD
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var server =
      context.parameterValue(SERVER);
    final var port =
      context.parameterValue(PORT);
    final var userName =
      context.parameterValue(USERNAME);
    final var password =
      context.parameterValue(PASSWORD);

    this.client()
      .login(
        InetSocketAddress.createUnresolved(
          server,
          port.intValue()
        ),
        TLS_DISABLED,
        new IdName(userName),
        password
    );

    return SUCCESS;
  }
}
