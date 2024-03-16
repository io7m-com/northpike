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


package com.io7m.northpike.agent.internal.worker;

import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentServerGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentWorkExecGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesServersType.ServerGetType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.internal.events.NPAgentDeleted;
import com.io7m.northpike.agent.internal.events.NPAgentEventType;
import com.io7m.northpike.agent.internal.events.NPAgentServerAssigned;
import com.io7m.northpike.agent.internal.events.NPAgentServerDeleted;
import com.io7m.northpike.agent.internal.events.NPAgentServerUnassigned;
import com.io7m.northpike.agent.internal.events.NPAgentServerUpdated;
import com.io7m.northpike.agent.internal.events.NPAgentUpdated;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerConnectionStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerConnectionStopped;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerExecutorStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerExecutorStopped;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerStopped;
import com.io7m.northpike.agent.internal.status.NPAgentConnectionStatusType;
import com.io7m.northpike.agent.internal.status.NPAgentConnectionStatusUnconfigured;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusType;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusUnconfigured;
import com.io7m.northpike.agent.internal.status.NPAgentWorkerStatus;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerDescription;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.tls.NPTLSContextServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.Flow;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorUnsupported;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_WORKEXEC_AVAILABLE;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NO_WORKEXEC_AVAILABLE_REMEDIATE;
import static com.io7m.northpike.strings.NPStringConstants.WORK_EXECUTOR;
import static java.util.Map.entry;

/**
 * A worker for a single agent.
 */

public final class NPAgentWorker
  implements NPAgentWorkerType, Runnable, Flow.Subscriber<NPEventType>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentWorker.class);

  private final RPServiceDirectoryType services;
  private final NPEventServiceType events;
  private final NPAgentDatabaseType database;
  private final NPStrings strings;
  private final NPTLSContextServiceType tlsContexts;
  private final List<? extends NPAWorkExecutorFactoryType> workExecs;
  private final NPAgentLocalName agentName;
  private final AtomicBoolean closed;
  private volatile Thread threadMain;
  private volatile NPAgentWorkerTaskMessaging connectionTask;
  private volatile Thread connectionTaskThread;
  private volatile Optional<NPAgentServerDescription> serverLatest;
  private volatile NPAgentWorkerTaskExecutor workExecTask;
  private volatile Thread workExecTaskThread;

  private NPAgentWorker(
    final RPServiceDirectoryType inServices,
    final NPEventServiceType inEvents,
    final NPAgentDatabaseType inDatabase,
    final NPStrings inStrings,
    final NPTLSContextServiceType inTlsContexts,
    final List<? extends NPAWorkExecutorFactoryType> inWorkExecs,
    final NPAgentLocalName inAgentName)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.tlsContexts =
      Objects.requireNonNull(inTlsContexts, "tlsContexts");
    this.workExecs =
      Objects.requireNonNull(inWorkExecs, "workExecs");
    this.agentName =
      Objects.requireNonNull(inAgentName, "agentName");
    this.closed =
      new AtomicBoolean(false);
    this.serverLatest =
      Optional.empty();
  }

  private static NPAgentWorkExecutorStatusType statusUpdateWorkExecutor(
    final NPAgentWorkerTaskExecutor execTask)
  {
    if (execTask != null) {
      return execTask.status();
    }
    return new NPAgentWorkExecutorStatusUnconfigured();
  }

  private static NPAgentConnectionStatusType statusUpdateConnection(
    final NPAgentWorkerTaskMessaging connTask)
  {
    if (connTask != null) {
      return connTask.status();
    }
    return new NPAgentConnectionStatusUnconfigured();
  }

  /**
   * Create a worker.
   *
   * @param services  The services
   * @param agentName The agent name
   *
   * @return A worker
   */

  public static NPAgentWorkerType create(
    final RPServiceDirectoryType services,
    final NPAgentLocalName agentName)
  {
    final var events =
      services.requireService(NPEventServiceType.class);
    final var database =
      services.requireService(NPAgentDatabaseType.class);
    final var strings =
      services.requireService(NPStrings.class);
    final var tlsContexts =
      services.requireService(NPTLSContextServiceType.class);
    final var workExecs =
      services.optionalServices(NPAWorkExecutorFactoryType.class);

    final var worker =
      new NPAgentWorker(
        services,
        events,
        database,
        strings,
        tlsContexts,
        workExecs,
        agentName
      );

    events.events().subscribe(worker);
    worker.start();
    return worker;
  }

  private void start()
  {
    this.threadMain = Thread.ofVirtual().start(this);
  }

  @Override
  public NPAgentLocalName agentName()
  {
    return this.agentName;
  }

  @Override
  public boolean workCanBeAccepted(
    final NPWorkItemIdentifier workItem)
  {
    Objects.requireNonNull(workItem, "workItem");

    final var workTask = this.workExecTask;
    if (workTask != null) {
      return workTask.workCanBeAccepted(workItem);
    }
    return false;
  }

  @Override
  public boolean workAccept(
    final NPAgentWorkItem workItem)
  {
    Objects.requireNonNull(workItem, "workItem");

    final var workTask = this.workExecTask;
    if (workTask != null) {
      return workTask.workAccept(workItem);
    }
    return false;
  }

  @Override
  public void workStarted(
    final NPAgentWorkItem workItem)
  {
    Objects.requireNonNull(workItem, "workItem");
  }

  @Override
  public void workCompleted(
    final NPAgentWorkItem workItem,
    final NPAWorkExecutionResult result)
  {
    Objects.requireNonNull(workItem, "workItem");
    Objects.requireNonNull(result, "result");

    final var t = this.connectionTask;
    if (t != null) {
      t.workCompleted(workItem.identifier(), result);
    }
  }

  @Override
  public void workUpdated(
    final NPAgentWorkItem workItem,
    final NPAWorkEvent item)
  {
    Objects.requireNonNull(workItem, "workItem");
    Objects.requireNonNull(item, "item");

    final var t = this.connectionTask;
    if (t != null) {
      t.workUpdated(workItem.identifier(), item);
    }
  }

  @Override
  public NPAgentWorkerStatus status()
  {
    final var execTask =
      this.workExecTask;
    final var connTask =
      this.connectionTask;

    return new NPAgentWorkerStatus(
      statusUpdateConnection(connTask),
      statusUpdateWorkExecutor(execTask)
    );
  }

  @Override
  public void close()
    throws Exception
  {
    MDC.put("AgentName", this.agentName.toString());

    if (this.closed.compareAndSet(false, true)) {
      try {
        LOG.debug("Worker stopping");
        this.threadMain.join();
      } finally {
        LOG.debug("Worker stopped");
      }
    }
  }

  @Override
  public void run()
  {
    MDC.put("AgentName", this.agentName.toString());
    LOG.debug("Worker started");

    this.workControllerRestart();
    this.connectionRestart();

    while (!this.closed.get()) {
      try {
        Thread.sleep(1_000L);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
    }
  }

  private void connectionRestart()
  {
    MDC.put("AgentName", this.agentName.toString());

    while (!this.closed.get()) {
      LOG.debug("Attempting to start connection");

      try {
        try (var dbConnection = this.database.openConnection()) {
          try (var transaction = dbConnection.openTransaction()) {
            final var agent =
              transaction.queries(AgentGetType.class)
                .execute(this.agentName);

            if (agent.isEmpty()) {
              LOG.debug("No agent definition; stopping connection.");
              this.connectionStop();
              return;
            }

            final var serverID =
              transaction.queries(AgentServerGetType.class)
                .execute(this.agentName);

            if (serverID.isEmpty()) {
              LOG.debug("No server assigned; stopping connection.");
              this.connectionStop();
              return;
            }

            final var server =
              transaction.queries(ServerGetType.class)
                .execute(serverID.get());

            if (server.isEmpty()) {
              LOG.debug("No server definition; stopping connection.");
              this.connectionStop();
              return;
            }

            this.serverLatest = server;
            this.connectionTask =
              NPAgentWorkerTaskMessaging.open(
                this,
                this.strings,
                this.tlsContexts,
                agent.get().keyPair(),
                server.get()
              );

            this.connectionTaskThread =
              Thread.ofVirtual()
                .start(this.connectionTask);

            this.events.emit(new NPAgentWorkerConnectionStarted(this.agentName));
            this.sendEnvironment();
            return;
          } catch (final InterruptedException e) {
            Thread.currentThread().interrupt();
          }
        }
      } catch (final Exception e) {
        LOG.error("Worker connection startup error: ", e);
        pauseBriefly();
      }
    }
  }

  private void connectionStop()
  {
    try {
      final var task = this.connectionTask;
      if (task != null) {
        try {
          task.close();
          this.events.emit(new NPAgentWorkerConnectionStopped(this.agentName));
        } catch (final NPAgentException e) {
          LOG.debug("Failed to close connection task: ", e);
        }
      }

      final var taskThread = this.connectionTaskThread;
      if (taskThread != null) {
        try {
          taskThread.join();
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
        }
      }
    } finally {
      this.connectionTaskThread = null;
      this.connectionTask = null;
    }
  }

  private void workControllerRestart()
  {
    MDC.put("AgentName", this.agentName.toString());

    while (!this.closed.get()) {
      LOG.debug("Attempting to start work controller");

      try {
        try (var dbConnection = this.database.openConnection()) {
          try (var transaction = dbConnection.openTransaction()) {
            final var workExecOpt =
              transaction.queries(AgentWorkExecGetType.class)
                .execute(this.agentName);

            if (workExecOpt.isEmpty()) {
              LOG.debug("No work exec definition; stopping work controller.");
              this.workControllerStop();
              return;
            }

            final var workConfig =
              workExecOpt.get();

            final var workExecutor =
              this.workExecs.stream()
                .filter(f -> {
                  try {
                    return f.isSupported();
                  } catch (final NPException e) {
                    LOG.debug("Work executor unsupported: ", e);
                    return false;
                  }
                })
                .filter(f -> Objects.equals(f.name(), workConfig.type()))
                .findFirst()
                .orElseThrow(() -> this.errorNoSuitableExecutor(workConfig))
                .createExecutor(this.services, this.agentName, workConfig);

            this.workExecTask =
              NPAgentWorkerTaskExecutor.open(this, workExecutor);
            this.workExecTaskThread =
              Thread.ofVirtual()
                .start(this.workExecTask);

            this.events.emit(new NPAgentWorkerExecutorStarted(this.agentName));
            this.sendEnvironment();
            return;
          } catch (final InterruptedException e) {
            Thread.currentThread().interrupt();
          }
        }
      } catch (final Exception e) {
        LOG.error("Work controller startup error: ", e);
        pauseBriefly();
      }
    }
  }

  private void sendEnvironment()
  {
    final var workExec =
      this.workExecTask;
    final var connTask =
      this.connectionTask;

    if (workExec != null && connTask != null) {
      try {
        connTask.setEnvironment(workExec.environment());
      } catch (final Exception e) {
        LOG.debug("Environment: ", e);
      }
    }
  }

  private NPException errorNoSuitableExecutor(
    final NPAWorkExecutorConfiguration workConfig)
  {
    return new NPException(
      this.strings.format(ERROR_NO_WORKEXEC_AVAILABLE),
      errorUnsupported(),
      Map.ofEntries(
        entry(this.strings.format(WORK_EXECUTOR), workConfig.type().toString())
      ),
      Optional.of(
        this.strings.format(ERROR_NO_WORKEXEC_AVAILABLE_REMEDIATE)
      )
    );
  }

  private void workControllerStop()
  {
    final var task = this.workExecTask;
    if (task != null) {
      try {
        task.close();
        this.events.emit(new NPAgentWorkerExecutorStopped(this.agentName));
      } catch (final NPAgentException e) {
        LOG.debug("Failed to close executor task: ", e);
      }
    }

    final var taskThread = this.workExecTaskThread;
    if (taskThread != null) {
      try {
        taskThread.join();
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
    }
  }

  private static void pauseBriefly()
  {
    try {
      Thread.sleep(2_000L);
    } catch (final InterruptedException e) {
      Thread.currentThread().interrupt();
    }
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPEventType item)
  {
    if (item instanceof final NPAgentEventType e) {
      this.onAgentEvent(e);
      return;
    }
  }

  private void onAgentEvent(
    final NPAgentEventType e)
  {
    switch (e) {
      case final NPAgentServerDeleted serverDeleted -> {
        this.onAgentEventServerDeleted(serverDeleted);
      }
      case final NPAgentServerUpdated serverUpdated -> {
        this.onAgentEventServerUpdated(serverUpdated);
      }
      case final NPAgentDeleted ignored -> {
        // Handled by the supervisor.
      }
      case final NPAgentUpdated agentUpdated -> {
        this.onAgentEventAgentUpdated(agentUpdated);
      }
      case final NPAgentWorkerStarted ignored -> {
        // Handled by the supervisor.
      }
      case final NPAgentWorkerStopped ignored -> {
        // Handled by the supervisor.
      }
      case final NPAgentWorkerConnectionStarted ignored -> {
        // Handled by the supervisor.
      }
      case final NPAgentWorkerConnectionStopped ignored -> {
        // Handled by the supervisor.
      }
      case final NPAgentWorkerExecutorStopped ignored -> {
        // Ignored
      }
      case final NPAgentWorkerExecutorStarted ignored -> {
        // Ignored
      }
      case final NPAgentServerAssigned serverAssigned -> {
        this.onAgentEventServerAssigned(serverAssigned);
      }
      case final NPAgentServerUnassigned serverUnassigned -> {
        this.onAgentEventServerUnassigned(serverUnassigned);
      }
    }
  }

  private void onAgentEventServerUnassigned(
    final NPAgentServerUnassigned serverUnassigned)
  {
    if (Objects.equals(this.agentName, serverUnassigned.agentName())) {
      this.connectionRestart();
    }
  }

  private void onAgentEventServerAssigned(
    final NPAgentServerAssigned serverAssigned)
  {
    if (Objects.equals(this.agentName, serverAssigned.agentName())) {
      this.connectionRestart();
    }
  }

  private void onAgentEventAgentUpdated(
    final NPAgentUpdated agentUpdated)
  {
    if (Objects.equals(agentUpdated.agentName(), this.agentName)) {
      this.workControllerRestart();
      return;
    }
  }

  private void onAgentEventServerUpdated(
    final NPAgentServerUpdated serverUpdated)
  {
    final var latest = this.serverLatest;
    if (latest.isPresent()) {
      if (Objects.equals(latest.get().id(), serverUpdated.serverID())) {
        this.connectionRestart();
      }
    }
  }

  private void onAgentEventServerDeleted(
    final NPAgentServerDeleted serverDeleted)
  {
    final var latest = this.serverLatest;
    if (latest.isPresent()) {
      if (Objects.equals(latest.get().id(), serverDeleted.serverID())) {
        this.connectionStop();
      }
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

  @Override
  public String toString()
  {
    return "[NPAgentWorker 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
