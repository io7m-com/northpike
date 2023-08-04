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

import com.io7m.northpike.agent.NPAgents;
import com.io7m.northpike.agent.api.NPAgentConfiguration;
import com.io7m.northpike.agent.configuration.NPAgentConfigurationFiles;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import com.io7m.quarrel.ext.logback.QLogback;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.stream.Stream;

import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * The "run" command.
 */

public final class NPACmdRun implements QCommandType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPACmdRun.class);

  private static final QParameterNamed1<Path> CONFIGURATION_FILE =
    new QParameterNamed1<>(
      "--configuration",
      List.of(),
      new QStringType.QConstant("The configuration file."),
      Optional.empty(),
      Path.class
    );

  private final QCommandMetadata metadata;

  /**
   * Construct a command.
   */

  public NPACmdRun()
  {
    this.metadata = new QCommandMetadata(
      "run",
      new QStringType.QConstant("Start the agent."),
      Optional.empty()
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return Stream.concat(
      Stream.of(CONFIGURATION_FILE),
      QLogback.parameters().stream()
    ).toList();
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    QLogback.configure(context);

    final var configurationFile =
      context.parameterValue(CONFIGURATION_FILE);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final NPAgentConfiguration configuration;
    try (var files =
           NPAgentConfigurationFiles.open(
             strings,
             configurationFile,
             parseStatus -> {
               switch (parseStatus.severity()) {
                 case PARSE_INFO -> {
                   LOG.info(
                     "{}:{}: {}",
                     Integer.valueOf(parseStatus.lexical().line()),
                     Integer.valueOf(parseStatus.lexical().column()),
                     parseStatus.message()
                   );
                 }
                 case PARSE_WARNING -> {
                   LOG.warn(
                     "{}:{}: {}",
                     Integer.valueOf(parseStatus.lexical().line()),
                     Integer.valueOf(parseStatus.lexical().column()),
                     parseStatus.message()
                   );
                 }
                 case PARSE_ERROR -> {
                   LOG.error(
                     "{}:{}: {}",
                     Integer.valueOf(parseStatus.lexical().line()),
                     Integer.valueOf(parseStatus.lexical().column()),
                     parseStatus.message()
                   );
                 }
               }
             })) {
      configuration = files.execute();
    }

    final var agents = new NPAgents();
    try (var agent = agents.createAgent(configuration)) {
      agent.start();

      while (true) {
        try {
          Thread.sleep(1_000L);
        } catch (final InterruptedException e) {
          break;
        }
      }
    }

    return SUCCESS;
  }

  @Override
  public QCommandMetadata metadata()
  {
    return this.metadata;
  }
}
