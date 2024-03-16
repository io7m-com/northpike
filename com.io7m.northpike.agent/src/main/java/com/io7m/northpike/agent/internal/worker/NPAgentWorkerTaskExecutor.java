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

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.internal.NPAgentResources;
import com.io7m.northpike.agent.internal.NPAgentTaskType;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusExecuting;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusIdle;
import com.io7m.northpike.agent.internal.status.NPAgentWorkExecutorStatusType;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutionType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.agents.NPAgentWorkItem;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;
import java.util.concurrent.Flow;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.agent.workexec.api.NPAWorkExecutionResult.FAILURE;

/**
 * The task that handles work for the agent.
 */

public final class NPAgentWorkerTaskExecutor implements NPAgentTaskType,
  Flow.Subscriber<NPAWorkEvent>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentWorkerTaskExecutor.class);

  private final AtomicBoolean closed;
  private final NPAgentWorkerType worker;
  private final NPAWorkExecutorType workExec;
  private final CloseableCollectionType<NPAgentException> resources;
  private final AtomicBoolean executing;
  private volatile ExecutingState executionState;

  private NPAgentWorkerTaskExecutor(
    final NPAgentWorkerType inWorker,
    final NPAWorkExecutorType inWorkExec,
    final CloseableCollectionType<NPAgentException> inResources)
  {
    this.worker =
      Objects.requireNonNull(inWorker, "inWorker");
    this.workExec =
      Objects.requireNonNull(inWorkExec, "workExec");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.closed =
      new AtomicBoolean(false);
    this.executing =
      new AtomicBoolean(false);
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final NPAWorkEvent event)
  {
    final var s = this.executionState;
    if (s != null) {
      this.worker.workUpdated(s.workItem, event);
    } else {
      LOG.warn("Received event with no execution statue.");
    }
  }

  @Override
  public void onError(
    final Throwable throwable)
  {
    LOG.debug("Event handling error: ", throwable);
  }

  @Override
  public void onComplete()
  {

  }

  /**
   * @return The current work executor status
   */

  public NPAgentWorkExecutorStatusType status()
  {
    final var s = this.executionState;
    if (s != null) {
      return new NPAgentWorkExecutorStatusExecuting(s.workItem.identifier());
    }
    return new NPAgentWorkExecutorStatusIdle();
  }

  private record ExecutingState(
    NPAgentWorkItem workItem,
    NPAWorkExecutionType execution,
    Thread thread)
  {
    ExecutingState
    {
      Objects.requireNonNull(workItem, "workItem");
      Objects.requireNonNull(execution, "execution");
      Objects.requireNonNull(thread, "thread");
    }
  }

  /**
   * The task that handles work for the agent.
   *
   * @param worker   The owning worker
   * @param workExec The work executor
   *
   * @return An agent
   *
   * @throws InterruptedException On interruption
   */

  public static NPAgentWorkerTaskExecutor open(
    final NPAgentWorkerType worker,
    final NPAWorkExecutorType workExec)
    throws InterruptedException
  {
    Objects.requireNonNull(worker, "worker");
    Objects.requireNonNull(workExec, "workExec");

    return new NPAgentWorkerTaskExecutor(
      worker,
      workExec,
      NPAgentResources.createResources()
    );
  }

  @Override
  public void run()
  {
    LOG.debug("Start");

    while (!this.isClosed()) {
      try {
        Thread.sleep(1_000L);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
    }
  }

  @Override
  public void close()
    throws NPAgentException
  {
    if (this.closed.compareAndSet(false, true)) {
      LOG.debug("Close");
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String name()
  {
    return "com.io7m.northpike.agent.work_controller";
  }

  /**
   * Fetch the current working environment and package it up as a command
   * to be sent to the server.
   *
   * @return The environment command
   *
   * @throws NPException On errors
   */

  public NPACommandCEnvironmentInfo environment()
    throws NPException
  {
    return new NPACommandCEnvironmentInfo(
      UUID.randomUUID(),
      this.workExec.environment(),
      this.workExec.systemProperties()
    );
  }

  /**
   * @param workItem The work item
   *
   * @return {@code true} if the agent can currently accept the given work
   */

  public boolean workCanBeAccepted(
    final NPWorkItemIdentifier workItem)
  {
    return !this.executing.get();
  }

  /**
   * Accept the given work item.
   *
   * @param workItem The work item
   *
   * @return {@code true} if the agent was able to accept the work
   */

  public boolean workAccept(
    final NPAgentWorkItem workItem)
  {
    if (this.executing.compareAndSet(false, true)) {
      try {
        final var execution =
          this.workExec.createExecution(workItem);

        execution.events().subscribe(this);

        this.executionState =
          new ExecutingState(
            workItem,
            execution,
            Thread.startVirtualThread(() -> {
              try {
                MDC.put("WorkExecutionID", workItem.identifier().toString());
                LOG.debug("Starting execution.");
                this.worker.workStarted(workItem);
                this.worker.workUpdated(workItem, eventStarted());

                try (execution) {
                  this.worker.workCompleted(workItem, execution.execute());
                } catch (final Throwable e) {
                  LOG.warn("Execution raised exception: ", e);
                  this.worker.workCompleted(workItem, FAILURE);
                }
              } finally {
                LOG.debug("Finished execution.");
                this.executing.set(false);
              }
            })
          );

        return true;
      } catch (final Exception e) {
        LOG.error("Failed to create work execution: ", e);
        this.executing.set(false);
        this.worker.workCompleted(workItem, FAILURE);
        return true;
      }
    }
    return false;
  }

  private static NPAWorkEvent eventStarted()
  {
    return new NPAWorkEvent(
      NPAWorkEvent.Severity.INFO,
      OffsetDateTime.now(),
      "Started...",
      Map.of(),
      Optional.empty()
    );
  }
}
