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

import com.io7m.anethum.slf4j.ParseStatusLogging;
import com.io7m.northpike.agent.NPAgentHosts;
import com.io7m.northpike.agent.api.NPAgentHostConfiguration;
import com.io7m.northpike.agent.configuration.NPACFiles;
import com.io7m.northpike.agent.configuration.NPACPreserveLexical;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

/**
 * The "run" command.
 */

public final class NPACmdRun implements QCommandType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPACmdRun.class);

  private final QCommandMetadata metadata;

  private static final QParameterNamed1<Path> CONFIGURATION =
    new QParameterNamed1<>(
      "--configuration",
      List.of(),
      new QStringType.QConstant("The configuration file."),
      Optional.empty(),
      Path.class
    );

  /**
   * Construct a command.
   */

  public NPACmdRun()
  {
    this.metadata = new QCommandMetadata(
      "run",
      new QStringType.QConstant("Run the agent."),
      Optional.empty()
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(CONFIGURATION);
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var configurationFilePath =
      context.parameterValue(CONFIGURATION);

    final var configurationParsers =
      new NPACFiles();

    final NPAgentHostConfiguration configuration =
      configurationParsers.parseFileWithContext(
        NPACPreserveLexical.PRESERVE_LEXICAL_INFORMATION,
        configurationFilePath,
        status -> ParseStatusLogging.logWithAll(LOG, status)
      );

    final var agentHosts = new NPAgentHosts();
    try (var agentHost = agentHosts.createHost(configuration)) {
      agentHost.start();

      while (true) {
        Thread.sleep(1_000L);
      }
    }
  }

  @Override
  public QCommandMetadata metadata()
  {
    return this.metadata;
  }
}
