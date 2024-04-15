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
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.metrics.LongCounter;
import io.opentelemetry.api.metrics.ObservableLongGauge;
import io.opentelemetry.api.metrics.ObservableLongMeasurement;

import java.time.Duration;
import java.util.Objects;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.Consumer;

import static io.opentelemetry.api.common.AttributeKey.stringKey;

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
  private volatile long assignmentsEnqueued;
  private volatile long agentsConnected;
  private volatile long usersConnected;
  private volatile long assignmentsExecuting;
  private volatile long archiveRequestsInProgress;
  private final ConcurrentLinkedQueue<AgentLatencyMeasurement> agentLatencyMeasurements;

  private record AgentLatencyMeasurement(
    NPAgentID agent,
    long nanos)
  {

  }

  /**
   * The metrics service.
   *
   * @param telemetry The underlying telemetry system
   */

  public NPMetricsService(
    final NPTelemetryServiceType telemetry)
  {
    Objects.requireNonNull(telemetry, "telemetry");

    this.isNoOp =
      telemetry.isNoOp();
    this.agentLatencyMeasurements =
      new ConcurrentLinkedQueue<>();

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
        "northpike_agents_connected",
        "The number of connected agents.",
        m -> m.record(this.agentsConnected)
      )
    );

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_users_connected",
        "The number of connected users.",
        m -> m.record(this.usersConnected)
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
        .setDescription("The number of archive service HTTP requests that resulted in 4xx failures.")
        .build();

    this.archive5xx =
      telemetry.meter()
        .counterBuilder("northpike_archive_http_responses_5xx")
        .setDescription("The number of archive service HTTP requests that resulted in 5xx failures.")
        .build();

    this.archive2xx =
      telemetry.meter()
        .counterBuilder("northpike_archive_http_responses_2xx")
        .setDescription("The number of archive service HTTP requests that resulted in 2xx status codes.")
        .build();

    this.resources.add(
      createLongGauge(
        telemetry,
        "northpike_archive_requests_in_progress",
        "The number of archive service requests in progress.",
        m -> m.record(this.archiveRequestsInProgress)
      )
    );

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_agent_latency")
        .setDescription("The latency for a given agent.")
        .ofLongs()
        .buildWithCallback(this::consumeAgentLatencyMeasurements)
    );
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

  private void consumeAgentLatencyMeasurements(
    final ObservableLongMeasurement measurement)
  {
    while (!this.agentLatencyMeasurements.isEmpty()) {
      final var latency = this.agentLatencyMeasurements.poll();
      measurement.record(
        latency.nanos,
        Attributes.of(stringKey("agent"), latency.agent.toString())
      );
    }
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
    final int count)
  {
    this.agentsConnected = count;
  }

  @Override
  public void setUsersConnected(
    final int count)
  {
    this.usersConnected = count;
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
  public void setAgentLatency(
    final NPAgentID agentId,
    final Duration duration)
  {
    if (this.isNoOp) {
      return;
    }

    this.agentLatencyMeasurements.add(
      new AgentLatencyMeasurement(agentId, duration.toNanos())
    );
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
