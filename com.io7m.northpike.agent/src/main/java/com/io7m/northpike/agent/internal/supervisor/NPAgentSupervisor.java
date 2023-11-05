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


package com.io7m.northpike.agent.internal.supervisor;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentListType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentListType.Parameters;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseType;
import com.io7m.northpike.agent.internal.NPAgentResources;
import com.io7m.northpike.agent.internal.events.NPAgentDeleted;
import com.io7m.northpike.agent.internal.events.NPAgentEventType;
import com.io7m.northpike.agent.internal.events.NPAgentServerDeleted;
import com.io7m.northpike.agent.internal.events.NPAgentServerUpdated;
import com.io7m.northpike.agent.internal.events.NPAgentUpdated;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerConnectionStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerConnectionStopped;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerExecutorStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerExecutorStopped;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerStarted;
import com.io7m.northpike.agent.internal.events.NPAgentWorkerStopped;
import com.io7m.northpike.agent.internal.worker.NPAgentWorker;
import com.io7m.northpike.agent.internal.worker.NPAgentWorkerType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Flow;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The main agent supervisor.
 */

public final class NPAgentSupervisor
  implements NPAgentSupervisorType, Flow.Subscriber<NPEventType>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPAgentSupervisor.class);

  private final RPServiceDirectoryType services;
  private final NPEventServiceType events;
  private final NPAgentDatabaseType database;
  private final ConcurrentHashMap<NPAgentLocalName, NPAgentWorkerType> workers;
  private final AtomicBoolean closed;
  private final CloseableCollectionType<NPAgentException> resources;

  private NPAgentSupervisor(
    final RPServiceDirectoryType inServices,
    final NPEventServiceType inEvents,
    final NPAgentDatabaseType inDatabase)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.database =
      Objects.requireNonNull(inDatabase, "database");

    this.workers =
      new ConcurrentHashMap<>();
    this.resources =
      NPAgentResources.createResources();
    this.closed =
      new AtomicBoolean(false);

    this.resources.add(() -> {
      this.workers.values().forEach(this::workerClose);
    });
  }

  /**
   * Create a supervisor.
   *
   * @param services The services
   *
   * @return A supervisor
   *
   * @throws NPException On errors
   */

  public static NPAgentSupervisorType create(
    final RPServiceDirectoryType services)
    throws NPException
  {
    final var events =
      services.requireService(NPEventServiceType.class);
    final var database =
      services.requireService(NPAgentDatabaseType.class);

    final var supervisor = new NPAgentSupervisor(services, events, database);
    events.events().subscribe(supervisor);
    supervisor.start();
    return supervisor;
  }

  private void workerClose(
    final NPAgentWorkerType worker)
  {
    try {
      worker.close();
      this.events.emit(new NPAgentWorkerStopped(worker.agentName()));
    } catch (final Exception e) {
      LOG.warn("Failed to close worker: ", e);
    }
  }

  private void start()
    throws NPAgentDatabaseException
  {
    try (var connection = this.database.openConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var names =
          transaction.queries(AgentListType.class)
            .execute(new Parameters(Optional.empty(), Long.MAX_VALUE));

        for (final var name : names) {
          this.workerStart(name);
        }
      }
    }
  }

  @Override
  public String description()
  {
    return "Agent supervisor service.";
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.resources.close();
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
      case final NPAgentServerDeleted ignored -> {
        // Handled by workers
      }
      case final NPAgentServerUpdated ignored -> {
        // Handled by workers
      }
      case final NPAgentDeleted agentDeleted -> {
        this.onAgentEventAgentDeleted(agentDeleted);
      }
      case final NPAgentUpdated agentUpdated -> {
        this.onAgentEventAgentUpdated(agentUpdated);
      }
      case final NPAgentWorkerStarted ignored -> {
        // Ignored
      }
      case final NPAgentWorkerStopped ignored -> {
        // Ignored
      }
      case final NPAgentWorkerConnectionStarted ignored -> {
        // Ignored
      }
      case final NPAgentWorkerConnectionStopped ignored -> {
        // Ignored
      }
      case final NPAgentWorkerExecutorStarted ignored -> {
        // Ignored
      }
      case final NPAgentWorkerExecutorStopped ignored -> {
        // Ignored
      }
    }
  }

  private void onAgentEventAgentUpdated(
    final NPAgentUpdated agentUpdated)
  {
    final var agentName = agentUpdated.agentName();
    if (!this.workers.containsKey(agentName)) {
      this.workerStart(agentName);
    }
  }

  private void workerStart(
    final NPAgentLocalName agentName)
  {
    this.workers.put(agentName, NPAgentWorker.create(this.services, agentName));
    this.events.emit(new NPAgentWorkerStarted(agentName));
  }

  private void onAgentEventAgentDeleted(
    final NPAgentDeleted agentDeleted)
  {
    final var existing =
      this.workers.remove(agentDeleted.agentName());

    if (existing != null) {
      this.workerClose(existing);
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
    return "[NPAgentSupervisor 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public Map<NPAgentLocalName, String> agentStatuses()
  {
    final var results =
      new HashMap<NPAgentLocalName, String>(this.workers.size());
    final var workersNow =
      List.copyOf(this.workers.values());

    for (final var worker : workersNow) {
      results.put(worker.agentName(), worker.status());
    }

    return Map.copyOf(results);
  }
}
