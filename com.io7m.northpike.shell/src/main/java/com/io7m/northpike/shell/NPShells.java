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

package com.io7m.northpike.shell;


import com.io7m.northpike.model.NPException;
import com.io7m.northpike.shell.internal.NPShell;
import com.io7m.northpike.shell.internal.NPShellCmdAgentGet;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelAssign;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelDelete;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelGet;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelPut;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelUnassign;
import com.io7m.northpike.shell.internal.NPShellCmdAgentPut;
import com.io7m.northpike.shell.internal.NPShellCmdAgentSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAgentSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAgentSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAuditSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAuditSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAuditSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdHelp;
import com.io7m.northpike.shell.internal.NPShellCmdLogin;
import com.io7m.northpike.shell.internal.NPShellCmdLogout;
import com.io7m.northpike.shell.internal.NPShellCmdPublicKeyDelete;
import com.io7m.northpike.shell.internal.NPShellCmdPublicKeyGet;
import com.io7m.northpike.shell.internal.NPShellCmdPublicKeyPut;
import com.io7m.northpike.shell.internal.NPShellCmdPublicKeySearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdPublicKeySearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdPublicKeySearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdRepositoryGet;
import com.io7m.northpike.shell.internal.NPShellCmdRepositoryPublicKeyAssign;
import com.io7m.northpike.shell.internal.NPShellCmdRepositoryPublicKeyUnassign;
import com.io7m.northpike.shell.internal.NPShellCmdRepositoryPublicKeysAssigned;
import com.io7m.northpike.shell.internal.NPShellCmdRepositoryPut;
import com.io7m.northpike.shell.internal.NPShellCmdRepositorySearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdRepositorySearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdRepositorySearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdSCMProvidersSupported;
import com.io7m.northpike.shell.internal.NPShellCmdSelf;
import com.io7m.northpike.shell.internal.NPShellCmdSet;
import com.io7m.northpike.shell.internal.NPShellCmdType;
import com.io7m.northpike.shell.internal.NPShellCmdUserSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdUserSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdUserSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdVersion;
import com.io7m.northpike.shell.internal.NPShellOptions;
import com.io7m.northpike.shell.internal.NPShellTerminalHolder;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.user_client.api.NPUserClientConfiguration;
import com.io7m.northpike.user_client.api.NPUserClientType;
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

public final class NPShells implements NPShellFactoryType
{
  /**
   * The basic shell.
   */

  public NPShells()
  {

  }

  @Override
  public NPShellType create(
    final NPShellConfiguration configuration)
    throws NPException
  {
    final var client =
      configuration.userClients()
        .createUserClient(
          new NPUserClientConfiguration(
            configuration.strings(),
            configuration.messageSizeLimit()
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
      NPUserClientType.class, client);
    services.register(
      NPShellOptions.class, options);
    services.register(
      NPShellTerminalHolder.class, new NPShellTerminalHolder(terminal));
    services.register(
      NPStrings.class, configuration.strings());

    final List<NPShellCmdType> commands =
      List.of(
        new NPShellCmdAgentGet(services),
        new NPShellCmdAgentLabelAssign(services),
        new NPShellCmdAgentLabelDelete(services),
        new NPShellCmdAgentLabelGet(services),
        new NPShellCmdAgentLabelPut(services),
        new NPShellCmdAgentLabelSearchBegin(services),
        new NPShellCmdAgentLabelSearchNext(services),
        new NPShellCmdAgentLabelSearchPrevious(services),
        new NPShellCmdAgentLabelUnassign(services),
        new NPShellCmdAgentPut(services),
        new NPShellCmdAgentSearchBegin(services),
        new NPShellCmdAgentSearchNext(services),
        new NPShellCmdAgentSearchPrevious(services),
        new NPShellCmdAuditSearchBegin(services),
        new NPShellCmdAuditSearchNext(services),
        new NPShellCmdAuditSearchPrevious(services),
        new NPShellCmdHelp(services),
        new NPShellCmdLogin(services),
        new NPShellCmdLogout(services),
        new NPShellCmdPublicKeyDelete(services),
        new NPShellCmdPublicKeyGet(services),
        new NPShellCmdPublicKeyPut(services),
        new NPShellCmdPublicKeySearchBegin(services),
        new NPShellCmdPublicKeySearchNext(services),
        new NPShellCmdPublicKeySearchPrevious(services),
        new NPShellCmdRepositoryGet(services),
        new NPShellCmdRepositoryPublicKeyAssign(services),
        new NPShellCmdRepositoryPublicKeyUnassign(services),
        new NPShellCmdRepositoryPublicKeysAssigned(services),
        new NPShellCmdRepositoryPut(services),
        new NPShellCmdRepositorySearchBegin(services),
        new NPShellCmdRepositorySearchNext(services),
        new NPShellCmdRepositorySearchPrevious(services),
        new NPShellCmdSCMProvidersSupported(services),
        new NPShellCmdSelf(services),
        new NPShellCmdSet(services),
        new NPShellCmdUserSearchBegin(services),
        new NPShellCmdUserSearchNext(services),
        new NPShellCmdUserSearchPrevious(services),
        new NPShellCmdVersion(services)
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
        .appName("northpike")
        .terminal(terminal)
        .completer(completer)
        .parser(parser)
        .history(history)
        .build();

    return new NPShell(
      services,
      terminal,
      writer,
      commandsNamed,
      reader
    );
  }
}
