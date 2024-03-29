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
import com.io7m.northpike.preferences.api.NPPreferencesServiceType;
import com.io7m.northpike.preferences.basic.NPPreferencesService;
import com.io7m.northpike.shell.commons.NPShellCmdType;
import com.io7m.northpike.shell.commons.NPShellConfirmationService;
import com.io7m.northpike.shell.commons.NPShellConfirmationServiceType;
import com.io7m.northpike.shell.commons.NPShellOptions;
import com.io7m.northpike.shell.commons.NPShellTerminalHolder;
import com.io7m.northpike.shell.internal.NPShell;
import com.io7m.northpike.shell.internal.NPShellCmdAgentDelete;
import com.io7m.northpike.shell.internal.NPShellCmdAgentDeleteConfirm;
import com.io7m.northpike.shell.internal.NPShellCmdAgentGet;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelAssign;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelDelete;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelGet;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelPut;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLabelUnassign;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLoginChallengeAgentCreate;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLoginChallengeDelete;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLoginChallengeSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLoginChallengeSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAgentLoginChallengeSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAgentPut;
import com.io7m.northpike.shell.internal.NPShellCmdAgentSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAgentSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAgentSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAgentWorkItems;
import com.io7m.northpike.shell.internal.NPShellCmdAgentsConnected;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentExecute;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentExecutionSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentExecutionSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentExecutionSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentGet;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentPut;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAssignmentSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdAuditSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdAuditSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdAuditSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdBookmarkList;
import com.io7m.northpike.shell.internal.NPShellCmdBookmarkLogin;
import com.io7m.northpike.shell.internal.NPShellCmdBookmarkPut;
import com.io7m.northpike.shell.internal.NPShellCmdBookmarkRemove;
import com.io7m.northpike.shell.internal.NPShellCmdHelp;
import com.io7m.northpike.shell.internal.NPShellCmdLogin;
import com.io7m.northpike.shell.internal.NPShellCmdLogout;
import com.io7m.northpike.shell.internal.NPShellCmdPlanDelete;
import com.io7m.northpike.shell.internal.NPShellCmdPlanDeleteConfirm;
import com.io7m.northpike.shell.internal.NPShellCmdPlanFormatsSupported;
import com.io7m.northpike.shell.internal.NPShellCmdPlanGet;
import com.io7m.northpike.shell.internal.NPShellCmdPlanPut;
import com.io7m.northpike.shell.internal.NPShellCmdPlanSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdPlanSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdPlanSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdPlanValidate;
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
import com.io7m.northpike.shell.internal.NPShellCmdToolExecutionDescriptionGet;
import com.io7m.northpike.shell.internal.NPShellCmdToolExecutionDescriptionPut;
import com.io7m.northpike.shell.internal.NPShellCmdToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdToolExecutionDescriptionSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdToolExecutionDescriptionSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdToolExecutionDescriptionValidate;
import com.io7m.northpike.shell.internal.NPShellCmdToolGet;
import com.io7m.northpike.shell.internal.NPShellCmdToolSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdToolSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdToolSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdUserSearchBegin;
import com.io7m.northpike.shell.internal.NPShellCmdUserSearchNext;
import com.io7m.northpike.shell.internal.NPShellCmdUserSearchPrevious;
import com.io7m.northpike.shell.internal.NPShellCmdVersion;
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
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorIo;

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
    services.register(
      NPShellConfirmationServiceType.class,
      new NPShellConfirmationService()
    );

    try {
      services.register(
        NPPreferencesServiceType.class,
        NPPreferencesService.openOrDefault(
          configuration.configurationDirectory()
            .resolve("preferences.xml")
        )
      );
    } catch (final IOException e) {
      throw new NPException(
        e.getMessage(),
        e,
        errorIo(),
        Map.of(),
        Optional.empty()
      );
    }

    final List<NPShellCmdType> commands =
      List.of(
        new NPShellCmdAgentDelete(services),
        new NPShellCmdAgentDeleteConfirm(services),
        new NPShellCmdAgentGet(services),
        new NPShellCmdAgentLabelAssign(services),
        new NPShellCmdAgentLabelDelete(services),
        new NPShellCmdAgentLabelGet(services),
        new NPShellCmdAgentLabelPut(services),
        new NPShellCmdAgentLabelSearchBegin(services),
        new NPShellCmdAgentLabelSearchNext(services),
        new NPShellCmdAgentLabelSearchPrevious(services),
        new NPShellCmdAgentLabelUnassign(services),
        new NPShellCmdAgentLoginChallengeAgentCreate(services),
        new NPShellCmdAgentLoginChallengeDelete(services),
        new NPShellCmdAgentLoginChallengeSearchBegin(services),
        new NPShellCmdAgentLoginChallengeSearchNext(services),
        new NPShellCmdAgentLoginChallengeSearchPrevious(services),
        new NPShellCmdAgentPut(services),
        new NPShellCmdAgentSearchBegin(services),
        new NPShellCmdAgentSearchNext(services),
        new NPShellCmdAgentSearchPrevious(services),
        new NPShellCmdAgentWorkItems(services),
        new NPShellCmdAgentsConnected(services),
        new NPShellCmdAssignmentExecute(services),
        new NPShellCmdAssignmentExecutionSearchBegin(services),
        new NPShellCmdAssignmentExecutionSearchNext(services),
        new NPShellCmdAssignmentExecutionSearchPrevious(services),
        new NPShellCmdAssignmentGet(services),
        new NPShellCmdAssignmentPut(services),
        new NPShellCmdAssignmentSearchBegin(services),
        new NPShellCmdAssignmentSearchNext(services),
        new NPShellCmdAssignmentSearchPrevious(services),
        new NPShellCmdAuditSearchBegin(services),
        new NPShellCmdAuditSearchNext(services),
        new NPShellCmdAuditSearchPrevious(services),
        new NPShellCmdBookmarkList(services),
        new NPShellCmdBookmarkLogin(services),
        new NPShellCmdBookmarkPut(services),
        new NPShellCmdBookmarkRemove(services),
        new NPShellCmdHelp(services),
        new NPShellCmdLogin(services),
        new NPShellCmdLogout(services),
        new NPShellCmdPlanDelete(services),
        new NPShellCmdPlanDeleteConfirm(services),
        new NPShellCmdPlanFormatsSupported(services),
        new NPShellCmdPlanGet(services),
        new NPShellCmdPlanPut(services),
        new NPShellCmdPlanSearchBegin(services),
        new NPShellCmdPlanSearchNext(services),
        new NPShellCmdPlanSearchPrevious(services),
        new NPShellCmdPlanValidate(services),
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
        new NPShellCmdToolExecutionDescriptionGet(services),
        new NPShellCmdToolExecutionDescriptionPut(services),
        new NPShellCmdToolExecutionDescriptionSearchBegin(services),
        new NPShellCmdToolExecutionDescriptionSearchNext(services),
        new NPShellCmdToolExecutionDescriptionSearchPrevious(services),
        new NPShellCmdToolExecutionDescriptionValidate(services),
        new NPShellCmdToolGet(services),
        new NPShellCmdToolSearchBegin(services),
        new NPShellCmdToolSearchNext(services),
        new NPShellCmdToolSearchPrevious(services),
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
