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


package com.io7m.northpike.server.internal.metrics;

import com.io7m.jmulticlose.core.CloseableCollection;
import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.jmulticlose.core.ClosingResourceFailedException;
import com.io7m.northpike.model.NPVersion;
import com.io7m.northpike.model.agents.NPAgentConnected;
import com.io7m.northpike.server.internal.repositories.NPRepositoryArchiveCreated;
import com.io7m.northpike.server.internal.repositories.NPRepositoryCloseFailed;
import com.io7m.northpike.server.internal.repositories.NPRepositoryClosed;
import com.io7m.northpike.server.internal.repositories.NPRepositoryConfigureFailed;
import com.io7m.northpike.server.internal.repositories.NPRepositoryConfigured;
import com.io7m.northpike.server.internal.repositories.NPRepositoryEventType;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceStarted;
import com.io7m.northpike.server.internal.repositories.NPRepositoryUpdateFailed;
import com.io7m.northpike.server.internal.repositories.NPRepositoryUpdated;
import com.io7m.northpike.server.internal.users.NPUserAuthenticated;
import com.io7m.northpike.server.internal.users.NPUserConnected;
import com.io7m.northpike.server.internal.users.NPUserDisconnected;
import com.io7m.northpike.server.internal.users.NPUserEventType;
import com.io7m.northpike.server.internal.users.NPUserMessageProcessed;
import com.io7m.northpike.server.internal.users.NPUserServiceStarted;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.metrics.LongHistogram;
import io.opentelemetry.api.metrics.ObservableLongGauge;
import io.opentelemetry.api.metrics.ObservableLongMeasurement;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.Flow;
import java.util.function.Consumer;

/**
 * The metrics service.
 */

public final class NPMetricsService implements NPMetricsServiceType
{
  private final CloseableCollectionType<ClosingResourceFailedException> resources;
  private final boolean isNoOp;
  private final LongCounter archive4xx;
  private final LongCounter archive5xx;
  private final LongCounter archive2xx;
  private final LongCounter repositoryCommitsAdded;
  private final LongCounter repositoryArchivesCreated;
  private final LongCounter repositoryUpdateFailures;
  private final LongHistogram repositoryUpdateTime;
  private final LongHistogram userMessageTime;
  private volatile long assignmentsEnqueued;
  private volatile long assignmentsExecuting;
  private volatile long archiveRequestsInProgress;
  private List<NPAgentConnected> agentsConnected = List.of();
  private List<com.io7m.northpike.model.NPUserConnected> usersConnected = List.of();

  /**
   * The metrics service.
   *
   * @param telemetry The underlying telemetry system
   * @param events    The event service
   *
   * @return The metrics service
   */

  public static NPMetricsServiceType create(
    final NPTelemetryServiceType telemetry,
    final NPEventServiceType events)
  {
    final var service = new NPMetricsService(telemetry);
    events.events().subscribe(new EventSubscriber(service));
    return service;
  }

  private static final class EventSubscriber
    implements Flow.Subscriber<NPEventType>
  {
    private final NPMetricsService service;

    EventSubscriber(
      final NPMetricsService inService)
    {
      this.service =
        Objects.requireNonNull(inService, "service");
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
      this.service.onEvent(item);
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

  private void onEvent(
    final NPEventType item)
  {
    switch (item) {
      case final NPRepositoryEventType repositoryEvent -> {
        this.onRepositoryEvent(repositoryEvent);
      }
      case final NPUserEventType userEvent -> {
        this.onUserEvent(userEvent);
      }
      default -> {
        // Nothing to do.
      }
    }
  }

  private void onUserEvent(
    final NPUserEventType event)
  {
    switch (event) {
      case final NPUserAuthenticated ignored -> {
        // Nothing to do
      }

      case final NPUserConnected ignored -> {
        // Nothing to do
      }

      case final NPUserDisconnected ignored -> {
        // Nothing to do
      }

      case final NPUserMessageProcessed r -> {
        this.userMessageTime.record(
          r.timeTaken().toMillis(),
          Attributes.builder()
            .put("MessageType", r.messageType())
            .build()
        );
      }

      case final NPUserServiceStarted ignored -> {
        // Nothing to do
      }
    }
  }

  private void onRepositoryEvent(
    final NPRepositoryEventType event)
  {
    switch (event) {
      case final NPRepositoryArchiveCreated r -> {
        this.repositoryArchivesCreated.add(
          1L,
          Attributes.builder()
            .put("RepositoryID", r.id().toString())
            .put("RepositoryURL", r.url().toString())
            .put("RepositoryProvider", r.provider().toString())
            .build()
        );
      }

      case final NPRepositoryCloseFailed ignored -> {
        // Nothing to do
      }

      case final NPRepositoryClosed ignored -> {
        // Nothing to do
      }

      case final NPRepositoryConfigureFailed ignored -> {
        // Nothing to do
      }

      case final NPRepositoryConfigured ignored -> {
        // Nothing to do
      }

      case final NPRepositoryServiceStarted ignored -> {
        // Nothing to do
      }

      case final NPRepositoryUpdateFailed r -> {
        this.repositoryUpdateFailures.add(
          1L,
          Attributes.builder()
            .put("RepositoryID", r.id().toString())
            .put("RepositoryURL", r.url().toString())
            .put("RepositoryProvider", r.provider().toString())
            .build()
        );
      }

      case final NPRepositoryUpdated r -> {
        this.repositoryCommitsAdded.add(
          r.commits(),
          Attributes.builder()
            .put("RepositoryID", r.id().toString())
            .put("RepositoryURL", r.url().toString())
            .put("RepositoryProvider", r.provider().toString())
            .build()
        );

        this.repositoryUpdateTime.record(
          r.timeTaken().toMillis(),
          Attributes.builder()
            .put("RepositoryID", r.id().toString())
            .put("RepositoryURL", r.url().toString())
            .put("RepositoryProvider", r.provider().toString())
            .build()
        );
      }
    }
  }

  /**
   * The metrics service.
   *
   * @param telemetry The underlying telemetry system
   */

  private NPMetricsService(
    final NPTelemetryServiceType telemetry)
  {
    Objects.requireNonNull(telemetry, "telemetry");

    this.isNoOp =
      telemetry.isNoOp();
    this.resources =
      CloseableCollection.create();

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_up",
        "A gauge that produces a constant value while the server is up.",
        m -> m.record(1L)
      )
    );

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_version",
        "A gauge that produces a constant version value.",
        m -> {
          m.record(
            1L,
            Attributes.builder()
              .put("Version", NPVersion.MAIN_VERSION)
              .put("Build", NPVersion.MAIN_BUILD)
              .build()
            );
        }
      )
    );

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_agents_latency",
        "The latency of the connected agents.",
        this::recordAgentsLatency
      )
    );

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_users_connected",
        "The number of connected users.",
        this::recordUsersConnected
      )
    );

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_assignments_executing",
        "The number of assignments currently executing.",
        m -> m.record(this.assignmentsExecuting)
      )
    );

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_assignments_enqueued",
        "The number of assignments currently enqueued.",
        m -> m.record(this.assignmentsEnqueued)
      )
    );

    this.archive4xx =
      telemetry.meter()
        .counterBuilder("northpike_archive_http_responses_4xx")
        .setDescription(
          "The number of archive service HTTP requests that resulted in 4xx failures.")
        .build();

    this.archive5xx =
      telemetry.meter()
        .counterBuilder("northpike_archive_http_responses_5xx")
        .setDescription(
          "The number of archive service HTTP requests that resulted in 5xx failures.")
        .build();

    this.archive2xx =
      telemetry.meter()
        .counterBuilder("northpike_archive_http_responses_2xx")
        .setDescription(
          "The number of archive service HTTP requests that resulted in 2xx status codes.")
        .build();

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_archive_requests_in_progress",
        "The number of archive service requests in progress.",
        m -> m.record(this.archiveRequestsInProgress)
      )
    );

    this.repositoryCommitsAdded =
      telemetry.meter()
        .counterBuilder("northpike_repository_commits_added")
        .setDescription(
          "The number of commits added to the database by the repository service.")
        .build();

    this.repositoryArchivesCreated =
      telemetry.meter()
        .counterBuilder("northpike_repository_archives_created")
        .setDescription(
          "The number of archives created by the repository service.")
        .build();

    this.repositoryUpdateFailures =
      telemetry.meter()
        .counterBuilder("northpike_repository_update_failures")
        .setDescription(
          "The number of repository update failures.")
        .build();

    this.repositoryUpdateTime =
      telemetry.meter()
        .histogramBuilder("northpike_repository_update_time")
        .setUnit("milliseconds")
        .setDescription("The time repositories are taking to update.")
        .ofLongs()
        .build();

    this.userMessageTime =
      telemetry.meter()
        .histogramBuilder("northpike_user_message_processing_time")
        .setUnit("milliseconds")
        .setDescription(
          "The time user protocol messages are taking to be processed.")
        .ofLongs()
        .build();
  }

  private void recordUsersConnected(
    final ObservableLongMeasurement m)
  {
    m.record((long) this.usersConnected.size());
  }

  private void recordAgentsLatency(
    final ObservableLongMeasurement m)
  {
    final var agentsNow = this.agentsConnected;
    for (final var agent : agentsNow) {
      m.record(
        agent.latency().toMillis(),
        Attributes.builder()
          .put("AgentID", agent.agentID().toString())
          .build()
      );
    }
  }

  private static ObservableLongGauge createLongGauge(
    final NPTelemetryServiceType telemetry,
    final String name,
    final String description,
    final Consumer<ObservableLongMeasurement> onMeasurement)
  {
    return telemetry.meter()
      .gaugeBuilder(name)
      .setDescription(description)
      .ofLongs()
      .buildWithCallback(onMeasurement);
  }

  @Override
  public String toString()
  {
    return "[NPMetricsService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public String description()
  {
    return "Metrics service.";
  }

  @Override
  public void close()
    throws Exception
  {
    this.resources.close();
  }

  @Override
  public void setAgentsConnected(
    final List<NPAgentConnected> agents)
  {
    this.agentsConnected = List.copyOf(agents);
  }

  @Override
  public void setUsersConnected(
    final List<com.io7m.northpike.model.NPUserConnected> users)
  {
    this.usersConnected = List.copyOf(users);
  }

  @Override
  public void setAssignmentsExecuting(
    final int count)
  {
    this.assignmentsExecuting = count;
  }

  @Override
  public void setAssignmentsQueueSize(
    final int count)
  {
    this.assignmentsEnqueued = count;
  }

  @Override
  public void onArchive4xx()
  {
    if (this.isNoOp) {
      return;
    }

    this.archive4xx.add(1L);
  }

  @Override
  public void onArchive2xx()
  {
    if (this.isNoOp) {
      return;
    }

    this.archive2xx.add(1L);
  }

  @Override
  public void onArchiveRequestStart()
  {
    if (this.isNoOp) {
      return;
    }

    ++this.archiveRequestsInProgress;
  }

  @Override
  public void onArchiveRequestStop()
  {
    if (this.isNoOp) {
      return;
    }

    this.archiveRequestsInProgress =
      Math.max(0L, this.archiveRequestsInProgress - 1L);
  }

  @Override
  public void onArchive5xx()
  {
    if (this.isNoOp) {
      return;
    }

    this.archive5xx.add(1L);
  }
}
