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
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;

import java.util.Objects;

/**
 * The metrics service.
 */

public final class NPMetricsService implements NPMetricsServiceType
{
  private final CloseableCollectionType<ClosingResourceFailedException> resources;
  private volatile int agentsConnected;
  private volatile int usersConnected;

  /**
   * The metrics service.
   *
   * @param telemetry The underlying telemetry system
   */

  public NPMetricsService(
    final NPTelemetryServiceType telemetry)
  {
    Objects.requireNonNull(telemetry, "telemetry");

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
}
