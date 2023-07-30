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
import com.io7m.northpike.server.internal.telemetry.NPTelemetryServiceType;
import io.opentelemetry.api.metrics.LongCounter;

import java.time.Duration;
import java.util.Objects;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * The metrics service.
 */

public final class NPMetricsService implements NPMetricsServiceType
{
  private final CloseableCollectionType<ClosingResourceFailedException> resources;
  private final LongCounter httpCount;
  private final LongCounter http2xx;
  private final LongCounter http4xx;
  private final LongCounter http5xx;
  private final LongCounter httpSizeRequest;
  private final LongCounter httpSizeResponse;
  private final ConcurrentLinkedQueue<Long> httpTimeNow;
  private volatile long loginSessions;

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

    this.httpTimeNow =
      new ConcurrentLinkedQueue<>();

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
        .gaugeBuilder("northpike_http_time")
        .setDescription(
          "The length of time requests are taking to process (nanoseconds).")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(maxOf(this.httpTimeNow));
        })
    );

    this.httpCount =
      telemetry.meter()
        .counterBuilder("northpike_http_requests")
        .setDescription("The number of HTTP requests.")
        .build();

    this.httpSizeRequest =
      telemetry.meter()
        .counterBuilder("northpike_http_requests_size")
        .setDescription("The total size of all HTTP requests so far.")
        .build();

    this.httpSizeResponse =
      telemetry.meter()
        .counterBuilder("northpike_http_responses_size")
        .setDescription("The total size of all HTTP responses so far.")
        .build();

    this.http2xx =
      telemetry.meter()
        .counterBuilder("northpike_http_responses_2xx")
        .setDescription(
          "The number of HTTP requests that resulted in 2xx successes.")
        .build();

    this.http4xx =
      telemetry.meter()
        .counterBuilder("northpike_http_responses_4xx")
        .setDescription(
          "The number of HTTP requests that resulted in 4xx failures.")
        .build();

    this.http5xx =
      telemetry.meter()
        .counterBuilder("northpike_http_responses_5xx")
        .setDescription(
          "The number of HTTP requests that resulted in 5xx failures.")
        .build();

    this.resources.add(
      telemetry.meter()
        .gaugeBuilder("northpike_sessions_active")
        .setDescription(
          "The number of active sessions.")
        .ofLongs()
        .buildWithCallback(measurement -> {
          measurement.record(this.loginSessions);
        })
    );
  }

  private static long maxOf(
    final ConcurrentLinkedQueue<Long> timeSamples)
  {
    var time = 0L;
    while (!timeSamples.isEmpty()) {
      time = Math.max(time, timeSamples.poll().longValue());
    }
    return time;
  }

  @Override
  public String toString()
  {
    return "[CAMetricsService %s]"
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
  public void onHttpRequested()
  {
    this.httpCount.add(1L);
  }

  @Override
  public void onHttp5xx()
  {
    this.http5xx.add(1L);
  }

  @Override
  public void onHttp2xx()
  {
    this.http2xx.add(1L);
  }

  @Override
  public void onHttp4xx()
  {
    this.http4xx.add(1L);
  }

  @Override
  public void onHttpRequestSize(
    final long size)
  {
    if (size == -1L) {
      return;
    }
    this.httpSizeRequest.add(size);
  }

  @Override
  public void onHttpResponseSize(
    final long size)
  {
    if (size == -1L) {
      return;
    }
    this.httpSizeResponse.add(size);
  }

  @Override
  public void onHttpResponseTime(
    final Duration time)
  {
    this.httpTimeNow.add(Long.valueOf(time.toNanos()));
  }

  @Override
  public void onLogin(
    final long sizeNow)
  {
    this.loginSessions = sizeNow;
  }

  @Override
  public void onLoginClosed(
    final long sizeNow)
  {
    this.loginSessions = sizeNow;
  }
}
