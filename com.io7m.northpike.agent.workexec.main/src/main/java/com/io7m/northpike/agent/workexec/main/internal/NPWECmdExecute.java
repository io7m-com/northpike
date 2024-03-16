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


package com.io7m.northpike.agent.workexec.main.internal;

import com.io7m.northpike.agent.locks.NPAgentResourceLockService;
import com.io7m.northpike.agent.locks.NPAgentResourceLockServiceType;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.local.NPWorkExecutorsLocal;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamed01;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.repetoir.core.RPServiceDirectoryWritableType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.ServiceLoader;
import java.util.concurrent.Flow;

import static com.io7m.northpike.agent.workexec.main.internal.NPWELogging.configureLoggingWork;
import static com.io7m.quarrel.core.QCommandStatus.FAILURE;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;
import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;
import static java.nio.file.StandardOpenOption.WRITE;

/**
 * The "execute" command.
 */

public final class NPWECmdExecute implements QCommandType,
  Flow.Subscriber<NPAWorkEvent>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPWECmdExecute.class);

  private final QCommandMetadata metadata;

  private static final QParameterNamed1<Path> WORK_ITEM_FILE =
    new QParameterNamed1<>(
      "--work-item",
      List.of(),
      new QStringType.QConstant("The work item file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<Path> WORK_DIRECTORY =
    new QParameterNamed1<>(
      "--work-directory",
      List.of(),
      new QStringType.QConstant("The work directory."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<Path> TMP_DIRECTORY =
    new QParameterNamed1<>(
      "--temporary-directory",
      List.of(),
      new QStringType.QConstant("The temporary directory."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<NPWELogFormat> LOG_FORMAT =
    new QParameterNamed1<>(
      "--log-format",
      List.of(),
      new QStringType.QConstant("The log format."),
      Optional.of(NPWELogFormat.TEXT),
      NPWELogFormat.class
    );

  private static final QParameterNamed01<Path> LOG_OUTPUT =
    new QParameterNamed01<>(
      "--log-output",
      List.of(),
      new QStringType.QConstant("The log output file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed1<NPAgentLocalName> AGENT =
    new QParameterNamed1<>(
      "--agent",
      List.of(),
      new QStringType.QConstant("The agent name."),
      Optional.empty(),
      NPAgentLocalName.class
    );

  private NPWELogFormat logFormat = NPWELogFormat.TEXT;
  private NPWELoggerType logger;

  /**
   * Construct a command.
   */

  public NPWECmdExecute()
  {
    this.metadata = new QCommandMetadata(
      "execute",
      new QStringType.QConstant("Execute the work item."),
      Optional.empty()
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      AGENT,
      LOG_FORMAT,
      LOG_OUTPUT,
      TMP_DIRECTORY,
      WORK_DIRECTORY,
      WORK_ITEM_FILE
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    this.logFormat =
      context.parameterValue(LOG_FORMAT);
    this.logger =
      switch (this.logFormat) {
        case TEXT -> NPWELoggerText.create(fileOutput(context));
        case BINARY -> NPWELoggerBinary.create(fileOutput(context));
      };

    this.logger.initialize();
    LOG.info(
      "Reconfiguring logging. Subsequent log messages will appear only on the configured output.");
    configureLoggingWork(this.logger);

    System.setOut(NPWELoggerPrintStream.create("STDOUT", this.logger));
    System.setErr(NPWELoggerPrintStream.create("STDERR", this.logger));

    MDC.put("ProcessID", Long.toUnsignedString(ProcessHandle.current().pid()));
    LOG.info("Start of log.");

    System.out.println("Standard output is active.");
    System.err.println("Standard error is active.");

    final var workItemFile =
      context.parameterValue(WORK_ITEM_FILE);
    final var workDirectory =
      context.parameterValue(WORK_DIRECTORY);
    final var tmpDirectory =
      context.parameterValue(TMP_DIRECTORY);
    final var agentName =
      context.parameterValue(AGENT);

    final var strings =
      NPStrings.create(Locale.getDefault());
    final NPAgentWorkItem workItem =
      NPWEItems.readWorkItem(strings, workItemFile);

    final var services = new RPServiceDirectory();
    services.register(NPStrings.class, strings);
    services.register(
      NPAgentResourceLockServiceType.class,
      NPAgentResourceLockService.create()
    );

    loadToolFactories(services);

    final var executors =
      new NPWorkExecutorsLocal();

    final var configuration =
      NPAWorkExecutorConfiguration.builder()
        .setExecutorType(executors.name())
        .setWorkDirectory(workDirectory)
        .setTemporaryDirectory(tmpDirectory)
        .build();

    final var executor =
      executors.createExecutor(services, agentName, configuration);

    try (var execution = executor.createExecution(workItem)) {
      execution.events().subscribe(this);
      return switch (execution.execute()) {
        case SUCCESS -> SUCCESS;
        case FAILURE -> FAILURE;
      };
    }
  }

  private static void loadToolFactories(
    final RPServiceDirectoryWritableType services)
  {
    final var loader =
      ServiceLoader.load(NPToolFactoryType.class);

    final var iterator =
      loader.iterator();
    while (iterator.hasNext()) {
      services.register(NPToolFactoryType.class, iterator.next());
    }
  }

  private static OutputStream fileOutput(
    final QCommandContextType context)
    throws IOException
  {
    final var fileOpt = context.parameterValue(LOG_OUTPUT);
    if (fileOpt.isPresent()) {
      return Files.newOutputStream(
        fileOpt.get(), CREATE, WRITE, TRUNCATE_EXISTING
      );
    }
    return System.out;
  }

  @Override
  public QCommandMetadata metadata()
  {
    return this.metadata;
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPAWorkEvent item)
  {
    try {
      this.logger.logWorkEvent(item);
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  @Override
  public void onError(
    final Throwable throwable)
  {

  }

  @Override
  public void onComplete()
  {

  }
}
