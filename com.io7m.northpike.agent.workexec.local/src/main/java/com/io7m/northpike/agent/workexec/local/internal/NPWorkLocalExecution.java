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


package com.io7m.northpike.agent.workexec.local.internal;

import com.io7m.jdownload.core.JDownloadErrorChecksumMismatch;
import com.io7m.jdownload.core.JDownloadErrorHTTP;
import com.io7m.jdownload.core.JDownloadErrorIO;
import com.io7m.jdownload.core.JDownloadErrorType;
import com.io7m.jdownload.core.JDownloadRequestType;
import com.io7m.jdownload.core.JDownloadRequests;
import com.io7m.jdownload.core.JDownloadSucceeded;
import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.locks.NPAgentResourceLockServiceType;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPToolReferenceName;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.strings.NPStringConstants;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.tools.api.NPToolEventTaskType;
import com.io7m.northpike.tools.api.NPToolEventType;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import com.io7m.northpike.tools.api.NPToolProcessOutput;
import com.io7m.northpike.tools.api.NPToolTaskCompletedFailure;
import com.io7m.northpike.tools.api.NPToolTaskCompletedSuccessfully;
import com.io7m.northpike.tools.api.NPToolTaskInProgress;
import com.io7m.northpike.tools.api.NPToolTaskStarted;
import com.io7m.northpike.tools.api.NPToolType;
import com.io7m.northpike.tools.common.NPToolArchives;
import com.io7m.northpike.tools.common.NPToolHTTPClients;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import com.io7m.seltzer.api.SStructuredErrorType;
import com.io7m.streamtime.core.STTransferStatistics;

import java.io.IOException;
import java.time.OffsetDateTime;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.Flow;
import java.util.concurrent.SubmissionPublisher;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import static com.io7m.northpike.agent.workexec.api.NPAWorkEvent.Severity.ERROR;
import static com.io7m.northpike.agent.workexec.api.NPAWorkEvent.Severity.INFO;
import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.FAILURE;
import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.SUCCESS;
import static com.io7m.northpike.agent.workexec.local.internal.NPFunctionSubscriber.createSubscriber;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_EXTERNAL_PROGRAM_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_RESOURCE_LOCK_TIMED_OUT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_TOOL_NOT_SUPPORTED;
import static com.io7m.northpike.strings.NPStringConstants.RESOURCE_NUMBERED;

/**
 * A work item being executed on the local machine.
 */

public final class NPWorkLocalExecution implements NPAWorkExecutionType
{
  private final CloseableCollectionType<NPException> resources;
  private final NPStrings strings;
  private final NPAgentResourceLockServiceType locks;
  private final Set<NPToolFactoryType> toolsSupported;
  private final NPAgentLocalName agentName;
  private final NPAWorkExecutorConfiguration configuration;
  private final NPAgentWorkItem workItem;
  private final AtomicBoolean closed;
  private final SubmissionPublisher<NPAWorkEvent> events;
  private final RPServiceDirectoryType services;
  private final HashMap<NPToolReferenceName, NPToolType> tools;
  private final HashMap<String, String> taskAttributes;
  private final NPToolArchives toolArchives;
  private final AtomicLong eventIndex;
  private NPWorkspace workspace;

  private NPWorkLocalExecution(
    final RPServiceDirectoryType inServices,
    final CloseableCollectionType<NPException> inResources,
    final NPStrings inStrings,
    final NPAgentResourceLockServiceType inLocks,
    final Set<NPToolFactoryType> inToolsSupported,
    final NPAgentLocalName inAgentName,
    final NPAWorkExecutorConfiguration inConfiguration,
    final NPAgentWorkItem inWorkItem)
  {
    this.services =
      Objects.requireNonNull(inServices, "inServices");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.locks =
      Objects.requireNonNull(inLocks, "locks");
    this.toolsSupported =
      Objects.requireNonNull(inToolsSupported, "toolsSupported");
    this.agentName =
      Objects.requireNonNull(inAgentName, "agentName");
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
    this.workItem =
      Objects.requireNonNull(inWorkItem, "workItem");
    this.events =
      new SubmissionPublisher<>();

    this.resources.add(this.events);

    this.eventIndex =
      new AtomicLong(1L);

    this.tools =
      new HashMap<>();
    this.toolArchives =
      new NPToolArchives(this.strings);

    this.closed =
      new AtomicBoolean(false);
    this.taskAttributes =
      new HashMap<>();
  }

  private void startTask(
    final String name)
  {
    this.startTask(name, UUID.randomUUID());
  }

  private void startTask(
    final String name,
    final UUID id)
  {
    this.taskAttributes.clear();
    this.taskAttributes.put("TaskName", name);
    this.taskAttributes.put("TaskID", id.toString());
  }

  /**
   * Create a new execution.
   *
   * @param services      The service directory
   * @param agentName     The agent that owns this execution
   * @param configuration The configuration
   * @param workItem      The work item
   *
   * @return A new execution
   */

  public static NPAWorkExecutionType create(
    final RPServiceDirectoryType services,
    final NPAWorkExecutorConfiguration configuration,
    final NPAgentLocalName agentName,
    final NPAgentWorkItem workItem)
  {
    Objects.requireNonNull(services, "services");
    Objects.requireNonNull(configuration, "configuration");
    Objects.requireNonNull(agentName, "agentName");
    Objects.requireNonNull(workItem, "workItem");

    final var strings =
      services.requireService(NPStrings.class);
    final var locks =
      services.requireService(NPAgentResourceLockServiceType.class);

    final var toolsSupported =
      new HashSet<NPToolFactoryType>(
        services.optionalServices(NPToolFactoryType.class)
      );

    final var resources =
      CloseableCollection.create(() -> {
        return new NPException(
          strings.format(NPStringConstants.ERROR_RESOURCE_CLOSING),
          NPStandardErrorCodes.errorResourceCloseFailed(),
          Map.of(),
          Optional.empty()
        );
      });

    return new NPWorkLocalExecution(
      services,
      resources,
      strings,
      locks,
      toolsSupported,
      agentName,
      configuration,
      workItem
    );
  }

  @Override
  public Flow.Publisher<NPAWorkEvent> events()
  {
    return this.events;
  }

  @Override
  public NPAWorkExecutionResult execute()
  {
    try {
      this.executeAnnounce();
      this.executeSetupWorkspace();
      this.executeInstallTools();
      this.executeDownloadArchive();
      this.executeTask();
      return SUCCESS;
    } catch (final Throwable e) {
      this.logException(e);
      return FAILURE;
    }
  }

  private void executeAnnounce()
  {
    this.startTask("Setup");
    this.setAttribute(
      "Assignment",
      "%s %s".formatted(
        this.workItem.identifier().assignmentExecutionId(),
        this.workItem.identifier().planElementName())
    );

    int index = 0;
    for (final var entry : this.workItem.lockResources()) {
      this.setAttribute(
        this.strings.format(RESOURCE_NUMBERED, Integer.valueOf(index)),
        entry.toString()
      );
      ++index;
    }

    this.setAttribute("LocalTime", OffsetDateTime.now());
    this.info("Starting execution of work item.");
  }

  private void executeDownloadArchive()
    throws InterruptedException, NPException
  {
    this.startTask("DownloadArchive");
    this.info("Downloading archive.");

    final var archiveLinks = this.workItem.archiveLinks();
    this.setAttribute("Archive", archiveLinks.sources());
    this.setAttribute("Checksum", archiveLinks.checksum());

    final var client =
      NPToolHTTPClients.create();

    final var outputFile =
      this.workspace.archiveDirectory().resolve("archive.tar.gz");
    final var outputTmpFile =
      this.workspace.archiveDirectory().resolve("archive.tar.gz.tmp");
    final var checksumFile =
      this.workspace.archiveDirectory().resolve("archive.sha512");
    final var checksumTmpFile =
      this.workspace.archiveDirectory().resolve("archive.sha512.tmp");

    final JDownloadRequestType request =
      JDownloadRequests.builder(
          client,
          archiveLinks.sources(),
          outputFile,
          outputTmpFile
        )
        .setRequestModifier(NPToolHTTPClients::setUserAgent)
        .setChecksumRequestModifier(NPToolHTTPClients::setUserAgent)
        .setTransferStatisticsReceiver(this::onDownloadInProgress)
        .setChecksumFromURL(
          archiveLinks.checksum(),
          "SHA-512",
          checksumFile,
          checksumTmpFile,
          this::onDownloadInProgress
        ).build();

    switch (request.execute()) {
      case final JDownloadErrorType error -> {
        switch (error) {
          case final JDownloadErrorChecksumMismatch checksumMismatch -> {
            this.setAttribute(
              "ChecksumExpected", checksumMismatch.hashExpected());
            this.setAttribute(
              "ChecksumReceived", checksumMismatch.hashReceived());
            this.setAttribute(
              "ChecksumAlgorithm", checksumMismatch.algorithm());
            this.error("Checksum mismatch.");
          }
          case final JDownloadErrorHTTP http -> {
            this.setAttribute("Status", Integer.valueOf(http.status()));
            this.setAttribute("OutputFile", http.outputFile());
            this.error("HTTP error.");
          }
          case final JDownloadErrorIO io -> {
            this.events.submit(
              new NPAWorkEvent(
                ERROR,
                OffsetDateTime.now(),
                this.nextEventIndex(),
                Objects.requireNonNullElse(
                  io.exception().getMessage(),
                  this.strings.format(ERROR_IO)
                ),
                this.taskAttributes,
                Optional.of(NPStoredException.ofException(io.exception()))
              )
            );
          }
        }
        throw this.errorArchiveDownloadFailed();
      }
      case final JDownloadSucceeded succeeded -> {
        this.toolArchives.unpackTarGZ(
          succeeded.outputFile(),
          this.workspace.sourceDirectory()
        );
      }
    }
  }

  private long nextEventIndex()
  {
    return this.eventIndex.getAndIncrement();
  }

  private void onDownloadInProgress(
    final STTransferStatistics transfer)
  {
    this.setAttribute(
      "Progress",
      Double.valueOf(transfer.percentNormalized().orElse(0.0)));

    this.events.submit(
      new NPAWorkEvent(
        INFO,
        OffsetDateTime.now(),
        this.nextEventIndex(),
        "Downloading archive...",
        this.taskAttributes,
        Optional.empty()
      )
    );
  }

  private void executeTask()
    throws NPException, InterruptedException
  {
    this.startTask("Execute");
    this.info("Executing task.");

    final var execution =
      this.workItem.toolExecution();
    final var ref =
      execution.toolReference().referenceName();

    this.setAttribute("ToolReference", ref);

    final var tool = this.tools.get(ref);
    if (tool == null) {
      throw this.errorNoSuchToolReference();
    }

    try (var ignored = this.locks.lockWithDefaultTimeout(
      this.agentName,
      this.workItem.lockResources()
    )) {
      final var result =
        tool.execute(
          this.workspace.sourceDirectory(),
          execution.environment(),
          execution.command()
        );

      if (result.exitCode() != 0) {
        throw this.errorToolExecutionFailed();
      }
    } catch (final TimeoutException e) {
      throw this.errorLockTimedOut(e);
    }
  }

  private NPException errorLockTimedOut(
    final TimeoutException e)
  {
    return new NPException(
      this.strings.format(ERROR_RESOURCE_LOCK_TIMED_OUT),
      e,
      NPStandardErrorCodes.errorResourceLockTimedOut(),
      Map.copyOf(this.taskAttributes),
      Optional.empty()
    );
  }

  private NPException errorArchiveDownloadFailed()
  {
    return new NPException(
      this.strings.format(ERROR_IO),
      NPStandardErrorCodes.errorIo(),
      Map.copyOf(this.taskAttributes),
      Optional.empty()
    );
  }

  private NPException errorToolExecutionFailed()
  {
    return new NPException(
      this.strings.format(ERROR_EXTERNAL_PROGRAM_FAILED),
      NPStandardErrorCodes.errorExternalProgramFailed(),
      Map.copyOf(this.taskAttributes),
      Optional.empty()
    );
  }

  private NPException errorNoSuchToolReference()
  {
    return new NPException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.copyOf(this.taskAttributes),
      Optional.empty()
    );
  }

  private NPException errorToolInstallUnsupported()
  {
    return new NPException(
      this.strings.format(ERROR_TOOL_NOT_SUPPORTED),
      NPStandardErrorCodes.errorUnsupported(),
      Map.copyOf(this.taskAttributes),
      Optional.empty()
    );
  }

  private void executeSetupWorkspace()
    throws IOException
  {
    this.startTask("SetupWorkspace");
    this.setAttribute("BaseDirectory", this.configuration.workDirectory());
    this.info("Setting up workspace.");

    this.workspace =
      this.resources.add(
        NPWorkspace.open(
          this.configuration.workDirectory(),
          this.workItem
        )
      );

    this.setAttribute("ToolsDirectory", this.workspace.toolsDirectory());
    this.setAttribute("SourceDirectory", this.workspace.sourceDirectory());
    this.setAttribute("ArchiveDirectory", this.workspace.archiveDirectory());
    this.info("Configured workspace.");
  }

  private void info(
    final String format,
    final Object... arguments)
  {
    try {
      this.events.submit(
        new NPAWorkEvent(
          INFO,
          OffsetDateTime.now(),
          this.nextEventIndex(),
          format.formatted(arguments),
          this.taskAttributes,
          Optional.empty()
        )
      );
    } catch (final Exception e) {
      // Nothing we can do.
    }
  }

  private void error(
    final String format,
    final Object... arguments)
  {
    try {
      this.events.submit(
        new NPAWorkEvent(
          ERROR,
          OffsetDateTime.now(),
          this.nextEventIndex(),
          format.formatted(arguments),
          this.taskAttributes,
          Optional.empty()
        )
      );
    } catch (final Exception e) {
      // Nothing we can do.
    }
  }

  private void logException(
    final Throwable e)
  {
    if (e instanceof final SStructuredErrorType<?> s) {
      this.taskAttributes.putAll(s.attributes());
    }

    try {
      this.events.submit(
        new NPAWorkEvent(
          ERROR,
          OffsetDateTime.now(),
          this.nextEventIndex(),
          Objects.requireNonNullElse(
            e.getMessage(),
            e.getClass().getCanonicalName()),
          this.taskAttributes,
          Optional.of(NPStoredException.ofException(e))
        )
      );
    } catch (final Exception ex) {
      // Nothing we can do.
    }
  }

  private void executeInstallTools()
    throws NPException, InterruptedException
  {
    this.startTask("InstallTools");
    this.info(
      "Installing %d required tools.",
      Integer.valueOf(this.workItem.toolsRequired().size())
    );

    for (final var toolRequired : this.workItem.toolsRequired()) {
      this.executeInstallTool(toolRequired);
    }
  }

  private void executeInstallTool(
    final NPToolReference toolRequired)
    throws NPException, InterruptedException
  {
    final var toolName =
      toolRequired.toolName();
    final var toolVersion =
      toolRequired.version();
    final var refName =
      toolRequired.referenceName();

    this.setAttribute("ToolReference", refName);
    this.setAttribute("ToolName", toolName);
    this.setAttribute("ToolVersion", toolVersion);

    this.info(
      "Installing required tool: %s %s (%s)",
      toolName,
      toolVersion,
      refName
    );

    for (final var toolFactory : this.toolsSupported) {
      if (toolFactory.supports(toolName, toolVersion)) {

        final var toolDirectory =
          this.workspace.toolsDirectory()
            .resolve(refName.value().value());

        final var tool =
          toolFactory.createTool(
            this.services,
            toolVersion,
            toolDirectory
          );

        tool.events().subscribe(createSubscriber(this::onToolEventReceived));
        tool.install();
        this.tools.put(refName, tool);
        return;
      }
    }

    throw this.errorToolInstallUnsupported();
  }

  private void setAttribute(
    final String name,
    final Object value)
  {
    this.taskAttributes.put(name, value.toString());
  }

  private void onToolEventReceived(
    final NPToolEventType event)
  {
    switch (event) {
      case final NPToolEventTaskType e -> {
        switch (e) {
          case final NPToolTaskCompletedFailure failure -> {
            this.taskAttributes.putAll(failure.exception().attributes());

            this.events.submit(new NPAWorkEvent(
              ERROR,
              OffsetDateTime.now(),
              this.nextEventIndex(),
              failure.exception().getMessage(),
              this.taskAttributes,
              Optional.of(NPStoredException.ofException(failure.exception()))
            ));
          }

          case final NPToolTaskCompletedSuccessfully success -> {
            this.events.submit(new NPAWorkEvent(
              INFO,
              OffsetDateTime.now(),
              this.nextEventIndex(),
              "Task completed successfully.",
              this.taskAttributes,
              Optional.empty()
            ));
          }

          case final NPToolTaskInProgress progress -> {
            this.events.submit(new NPAWorkEvent(
              INFO,
              OffsetDateTime.now(),
              this.nextEventIndex(),
              "Task in progress (%.2f)".formatted(
                Double.valueOf(progress.progress() * 100.0)
              ),
              this.taskAttributes,
              Optional.empty()
            ));
          }

          case final NPToolTaskStarted started -> {
            this.taskAttributes.put(
              "TaskName", this.strings.format(started.name()));
            this.taskAttributes.put(
              "TaskID", started.taskId().toString());

            this.events.submit(new NPAWorkEvent(
              INFO,
              OffsetDateTime.now(),
              this.nextEventIndex(),
              "Task started.",
              this.taskAttributes,
              Optional.empty()
            ));
          }
        }
      }

      case final NPToolProcessOutput output -> {
        this.setAttribute("ProcessID", output.processId());
        this.setAttribute("ProcessName", output.processName());

        this.events.submit(new NPAWorkEvent(
          INFO,
          OffsetDateTime.now(),
          this.nextEventIndex(),
          output.text(),
          this.taskAttributes,
          Optional.empty()
        ));
      }
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }
}
