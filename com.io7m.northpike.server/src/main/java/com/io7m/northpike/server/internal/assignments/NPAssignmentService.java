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


package com.io7m.northpike.server.internal.assignments;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.metrics.NPMetricsServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

import java.util.List;
import java.util.Objects;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;

/**
 * The assignment service.
 */

public final class NPAssignmentService implements NPAssignmentServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAssignmentService.class);

  private final AtomicBoolean closed;
  private final RPServiceDirectoryType services;
  private final CloseableCollectionType<NPServerException> resources;
  private final NPDatabaseType database;
  private final NPTelemetryServiceType telemetry;
  private final NPStrings strings;
  private final ExecutorService mainExecutor;
  private final NPMetricsServiceType metrics;
  private final LinkedBlockingQueue<EnqueuedRequest> queue;
  private final ConcurrentHashMap<NPAssignmentExecutionRequest, NPAssignmentTask> tasks;

  private NPAssignmentService(
    final RPServiceDirectoryType inServices,
    final CloseableCollectionType<NPServerException> inResources,
    final NPDatabaseType inDatabase,
    final NPTelemetryServiceType inTelemetry,
    final NPStrings inStrings,
    final ExecutorService inMainExecutor,
    final NPMetricsServiceType inMetrics)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.mainExecutor =
      Objects.requireNonNull(inMainExecutor, "mainExecutor");
    this.metrics =
      Objects.requireNonNull(inMetrics, "metrics");

    this.closed =
      new AtomicBoolean(false);

    this.tasks =
      new ConcurrentHashMap<>();
    this.queue =
      new LinkedBlockingQueue<>();
  }

  /**
   * @param services The service directory
   *
   * @return A new assignment service
   */

  public static NPAssignmentServiceType create(
    final RPServiceDirectoryType services)
  {
    final var database =
      services.requireService(NPDatabaseType.class);
    final var telemetry =
      services.requireService(NPTelemetryServiceType.class);
    final var metrics =
      services.requireService(NPMetricsServiceType.class);
    final var strings =
      services.requireService(NPStrings.class);

    final var resources =
      NPServerResources.createResources();

    final var mainExecutor =
      resources.add(
        Executors.newThreadPerTaskExecutor(
          Thread.ofVirtual()
            .name("com.io7m.northpike.assignment-", 0L)
            .factory()
        )
      );

    final var service =
      new NPAssignmentService(
        services,
        resources,
        database,
        telemetry,
        strings,
        mainExecutor,
        metrics
      );

    mainExecutor.execute(service::start);
    return service;
  }

  private void start()
  {
    this.cancelOldAssignments();
    this.run();
  }

  private void run()
  {
    while (!this.isClosed()) {
      try {
        EnqueuedRequest request = null;
        try {
          request = this.queue.poll(1L, TimeUnit.SECONDS);
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
        }

        if (request != null) {
          this.metrics.setAssignmentsQueueSize(this.queue.size());
          final var savedRequest = request;
          this.mainExecutor.execute(() -> {
            this.executeRequestInSpan(savedRequest);
          });
        }
      } catch (final Exception e) {
        LOG.error("Error processing assignment queue: ", e);
      }
    }
  }

  private void executeRequestInSpan(
    final EnqueuedRequest enqueuedRequest)
  {
    final var request =
      enqueuedRequest.request;
    final var executionId =
      enqueuedRequest.executionId;

    final var span =
      this.telemetry.tracer()
        .spanBuilder("AssignmentExecution")
        .setAttribute("Assignment", request.assignment().toString())
        .setAttribute("AssignmentExecutionID", executionId.toString())
        .setAttribute("Commit", request.commit().value())
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.executeRequest(request, executionId);
      enqueuedRequest.future.complete(null);
    } catch (final Throwable e) {
      NPTelemetryServiceType.recordSpanException(e);
      this.recordExceptionText(executionId, e);
      enqueuedRequest.future.completeExceptionally(e);
    } finally {
      span.end();
    }
  }

  private void recordExceptionText(
    final NPAssignmentExecutionID executionId,
    final Throwable e)
  {
    try (var connection =
           this.database.openConnection(NORTHPIKE)) {
      try (var transaction =
             connection.openTransaction()) {
        NPAssignmentLogging.recordException(transaction, executionId, e);
        transaction.commit();
      }
    } catch (final NPDatabaseException ex) {
      NPTelemetryServiceType.recordSpanException(ex);
    }
  }

  private void executeRequest(
    final NPAssignmentExecutionRequest request,
    final NPAssignmentExecutionID executionId)
  {
    MDC.put("Assignment", request.assignment().toString());
    MDC.put("AssignmentExecutionID", executionId.toString());
    MDC.put("Commit", request.commit().value());

    if (this.tasks.containsKey(request)) {
      LOG.info("Assignment is already executing.");
      return;
    }

    final var task =
      NPAssignmentTask.create(this.services, request, executionId);

    try (task) {
      this.tasks.put(request, task);
      this.metrics.setAssignmentsExecuting(this.tasks.size());
      task.run();
    } finally {
      this.tasks.remove(request);
      this.metrics.setAssignmentsExecuting(this.tasks.size());
    }
  }

  private void cancelOldAssignments()
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("CancelOldAssignments")
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.cancelOldAssignmentsInSpan();
    } finally {
      span.end();
    }
  }

  private void cancelOldAssignmentsInSpan()
  {
    try (var conn = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = conn.openTransaction()) {
        final var updated =
          transaction.queries(NPDatabaseQueriesAssignmentsType.ExecutionsCancelAllType.class)
            .execute(NPDatabaseUnit.UNIT);
        LOG.info("Cancelled {} old assignment executions.", updated);
      }
    } catch (final NPDatabaseException e) {
      NPTelemetryServiceType.recordSpanException(e);
    }
  }

  record EnqueuedRequest(
    NPAssignmentExecutionRequest request,
    NPAssignmentExecutionID executionId,
    CompletableFuture<NPAssignmentExecutionStateType> future)
  {

  }

  @Override
  public NPExecutionInProgress requestExecution(
    final NPAssignmentExecutionRequest request)
  {
    Objects.requireNonNull(request, "request");

    final var executionId = new NPAssignmentExecutionID(UUID.randomUUID());
    final var future = new CompletableFuture<NPAssignmentExecutionStateType>();
    this.queue.add(new EnqueuedRequest(request, executionId, future));
    this.metrics.setAssignmentsQueueSize(this.queue.size());
    return new NPExecutionInProgress(request, executionId, future);
  }

  @Override
  public List<NPAssignmentExecutionRequest> requestsEnqueued()
  {
    return this.queue.stream()
      .map(x -> x.request)
      .toList();
  }

  @Override
  public void close()
    throws NPException
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
    }
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String description()
  {
    return "Assignment execution service.";
  }

  @Override
  public String toString()
  {
    return "[NPAssignmentService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
