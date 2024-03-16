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
import io.opentelemetry.api.metrics.ObservableLongMeasurement;

import java.time.Duration;
import java.util.Objects;
import java.util.concurrent.ConcurrentLinkedQueue;

import static io.opentelemetry.api.common.AttributeKey.stringKey;

/**
 * The metrics service.
 */

public final class NPMetricsService implements NPMetricsServiceType
{
  private final CloseableCollectionType<ClosingResourceFailedException> resources;
  private final boolean isNoOp;
  private volatile int assignmentsEnqueued;
  private volatile int agentsConnected;
  private volatile int usersConnected;
  private volatile int assignmentsExecuting;
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
      telemetry.meter()
        .gaugeBuilder("northpike_up")
        .setDescription(
          "A gauge that produces a constant value while the server is up.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(1L);
        })
    );

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_agents_connected")
        .setDescription(
          "The number of connected agents.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(Integer.toUnsignedLong(this.agentsConnected));
        })
    );

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_users_connected")
        .setDescription(
          "The number of connected users.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(Integer.toUnsignedLong(this.usersConnected));
        })
    );

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_assignments_executing")
        .setDescription(
          "The number of assignments currently executing.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(Integer.toUnsignedLong(this.assignmentsExecuting));
        })
    );

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_assignments_enqueued")
        .setDescription(
          "The number of assignments currently enqueued.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(Integer.toUnsignedLong(this.assignmentsEnqueued));
        })
    );

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_agent_latency")
        .setDescription("The latency for a given agent.")
        .ofLongs()
        .buildWithCallback(this::consumeAgentLatencyMeasurements)
    );
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
}
