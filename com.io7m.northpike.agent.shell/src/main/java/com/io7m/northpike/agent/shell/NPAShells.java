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

package com.io7m.northpike.agent.shell;


import com.io7m.northpike.agent.console_client.api.NPAConsoleClientConfiguration;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientType;
import com.io7m.northpike.agent.shell.internal.NPAShell;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdAgentCreate;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdAgentDelete;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdAgentGet;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdAgentList;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdAgentServerAssign;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdAgentServerUnassign;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdHelp;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdLogin;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdLogout;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdServerDelete;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdServerGet;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdServerList;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdServerPut;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdServerSetTLS;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdSet;
import com.io7m.northpike.agent.shell.internal.NPAShellCmdVersion;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.shell.commons.NPShellCmdType;
import com.io7m.northpike.shell.commons.NPShellOptions;
import com.io7m.northpike.shell.commons.NPShellTerminalHolder;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.repetoir.core.RPServiceDirectory;
import org.jline.reader.LineReaderBuilder;
import org.jline.reader.impl.DefaultParser;
import org.jline.reader.impl.completer.AggregateCompleter;
import org.jline.reader.impl.completer.ArgumentCompleter;
import org.jline.reader.impl.completer.StringsCompleter;
import org.jline.reader.impl.history.DefaultHistory;
import org.jline.terminal.TerminalBuilder;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * The basic shell.
 */

public final class NPAShells implements NPAShellFactoryType
{
  /**
   * The basic shell.
   */

  public NPAShells()
  {

  }

  @Override
  public NPAShellType create(
    final NPAShellConfiguration configuration)
    throws NPException
  {
    final var client =
      configuration.consoleClients()
        .createConsoleClient(
          new NPAConsoleClientConfiguration(
            configuration.strings()
          )
        );

    final var terminal =
      configuration.terminal()
        .orElseGet(() -> {
          try {
            return TerminalBuilder.terminal();
          } catch (final IOException e) {
            throw new UncheckedIOException(e);
          }
        });
    final var writer =
      terminal.writer();

    final var options =
      new NPShellOptions(terminal);

    final var services = new RPServiceDirectory();
    services.register(
      NPAConsoleClientType.class, client);
    services.register(
      NPShellOptions.class, options);
    services.register(
      NPShellTerminalHolder.class, new NPShellTerminalHolder(terminal));
    services.register(
      NPStrings.class, configuration.strings());

    final List<NPShellCmdType> commands =
      List.of(
        new NPAShellCmdAgentCreate(services),
        new NPAShellCmdAgentDelete(services),
        new NPAShellCmdAgentGet(services),
        new NPAShellCmdAgentList(services),
        new NPAShellCmdAgentServerAssign(services),
        new NPAShellCmdAgentServerUnassign(services),
        new NPAShellCmdHelp(services),
        new NPAShellCmdLogin(services),
        new NPAShellCmdLogout(services),
        new NPAShellCmdServerDelete(services),
        new NPAShellCmdServerGet(services),
        new NPAShellCmdServerList(services),
        new NPAShellCmdServerPut(services),
        new NPAShellCmdServerSetTLS(services),
        new NPAShellCmdSet(services),
        new NPAShellCmdVersion(services)
      );

    final var commandsNamed =
      commands.stream()
        .collect(Collectors.toMap(
          e -> e.metadata().name(),
          Function.identity())
        );

    final var history =
      new DefaultHistory();
    final var parser =
      new DefaultParser();

    final var completer =
      new AggregateCompleter(
        commands.stream()
          .map(c -> {
            return new ArgumentCompleter(
              new StringsCompleter(c.metadata().name()),
              c.completer()
            );
          })
          .collect(Collectors.toList())
      );

    final var reader =
      LineReaderBuilder.builder()
        .appName("northpike-agent-shell")
        .terminal(terminal)
        .completer(completer)
        .parser(parser)
        .history(history)
        .build();

    return new NPAShell(
      services,
      terminal,
      writer,
      commandsNamed,
      reader
    );
  }
}
