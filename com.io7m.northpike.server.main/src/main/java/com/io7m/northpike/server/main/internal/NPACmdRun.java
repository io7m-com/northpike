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


package com.io7m.northpike.server.main.internal;

import com.io7m.anethum.slf4j.ParseStatusLogging;
import com.io7m.canonmill.core.CMKeyStoreProvider;
import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.postgres.NPPGDatabases;
import com.io7m.northpike.server.NPServers;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.configuration.NPSCFile;
import com.io7m.northpike.server.configuration.NPSCFiles;
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
import java.security.Security;
import java.time.Clock;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.stream.Stream;

import static com.io7m.northpike.database.api.NPDatabaseCreate.CREATE_DATABASE;
import static com.io7m.northpike.database.api.NPDatabaseCreate.DO_NOT_CREATE_DATABASE;
import static com.io7m.northpike.database.api.NPDatabaseUpgrade.DO_NOT_UPGRADE_DATABASE;
import static com.io7m.northpike.database.api.NPDatabaseUpgrade.UPGRADE_DATABASE;
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
      new QStringType.QConstant("Start the server."),
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

    Security.addProvider(new CMKeyStoreProvider());

    final var configurationFile =
      context.parameterValue(CONFIGURATION_FILE);

    final var strings =
      NPStrings.create(Locale.ROOT);

    final NPSCFile configuration;
    try (var files =
           NPSCFiles.open(
             configurationFile,
             status -> ParseStatusLogging.logMinimal(LOG, status))) {
      configuration = files.execute();
    }

    final var dbFileConfig =
      configuration.databaseConfiguration();

    final var databaseConfiguration =
      new NPDatabaseConfiguration(
        dbFileConfig.ownerRoleName(),
        dbFileConfig.ownerRolePassword(),
        dbFileConfig.workerRolePassword(),
        dbFileConfig.readerRolePassword(),
        dbFileConfig.address(),
        dbFileConfig.port(),
        dbFileConfig.databaseName(),
        dbFileConfig.create() ? CREATE_DATABASE : DO_NOT_CREATE_DATABASE,
        dbFileConfig.upgrade() ? UPGRADE_DATABASE : DO_NOT_UPGRADE_DATABASE,
        dbFileConfig.useTLS(),
        dbFileConfig.databaseLanguage(),
        Clock.systemUTC(),
        strings
      );

    final var serverConfiguration =
      new NPServerConfiguration(
        Locale.getDefault(),
        Clock.systemUTC(),
        strings,
        new NPPGDatabases(),
        databaseConfiguration,
        configuration.directoryConfiguration(),
        configuration.idstoreConfiguration(),
        configuration.agentConfiguration(),
        configuration.archiveConfiguration(),
        configuration.userConfiguration(),
        configuration.maintenanceConfiguration(),
        configuration.openTelemetry()
      );

    final var servers = new NPServers();
    try (var server = servers.createServer(serverConfiguration)) {
      server.start();

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
