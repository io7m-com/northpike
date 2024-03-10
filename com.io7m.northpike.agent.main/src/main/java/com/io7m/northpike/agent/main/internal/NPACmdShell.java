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


package com.io7m.northpike.agent.main.internal;

import com.io7m.northpike.agent.console_client.NPAConsoleClients;
import com.io7m.northpike.agent.shell.NPAShellConfiguration;
import com.io7m.northpike.agent.shell.NPAShells;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import com.io7m.quarrel.ext.logback.QLogback;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.bridge.SLF4JBridgeHandler;

import java.util.List;
import java.util.Locale;
import java.util.Optional;

/**
 * The "shell" command.
 */

public final class NPACmdShell implements QCommandType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPACmdShell.class);

  private final QCommandMetadata metadata;

  /**
   * Construct a command.
   */

  public NPACmdShell()
  {
    this.metadata = new QCommandMetadata(
      "shell",
      new QStringType.QConstant("Run the agent shell."),
      Optional.empty()
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return QLogback.plusParameters(List.of());
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    System.setProperty("org.jooq.no-tips", "true");
    System.setProperty("org.jooq.no-logo", "true");

    SLF4JBridgeHandler.removeHandlersForRootLogger();
    SLF4JBridgeHandler.install();

    QLogback.configure(context);

    final var configuration =
      new NPAShellConfiguration(
        Locale.getDefault(),
        new NPAConsoleClients(),
        NPStrings.create(Locale.getDefault()),
        Optional.empty()
      );

    final var shells = new NPAShells();
    try (var shell = shells.create(configuration)) {
      shell.run();
      return switch (shell.exitCode()) {
        case 0 -> QCommandStatus.SUCCESS;
        default -> QCommandStatus.FAILURE;
      };
    }
  }

  @Override
  public QCommandMetadata metadata()
  {
    return this.metadata;
  }
}
