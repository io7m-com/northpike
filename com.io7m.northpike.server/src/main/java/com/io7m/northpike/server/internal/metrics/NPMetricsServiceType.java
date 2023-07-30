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

import com.io7m.repetoir.core.RPServiceType;

import java.time.Duration;

/**
 * The interface exposed by the metrics service.
 */

public interface NPMetricsServiceType extends AutoCloseable, RPServiceType
{
  /**
   * An HTTP request was received.
   */

  void onHttpRequested();

  /**
   * An HTTP request resulted in a 5xx error.
   */

  void onHttp5xx();

  /**
   * An HTTP request resulted in a 2xx success.
   */

  void onHttp2xx();

  /**
   * An HTTP request resulted in a 4xx error.
   */

  void onHttp4xx();

  /**
   * An HTTP request was received of a given size.
   *
   * @param size The size
   */

  void onHttpRequestSize(
    long size);

  /**
   * An HTTP response was produced of a given size.
   *
   * @param size The size
   */

  void onHttpResponseSize(
    long size);

  /**
   * An HTTP response was produced in the given time.
   *
   * @param time The time
   */

  void onHttpResponseTime(
    Duration time);

  /**
   * A login session was created.
   *
   * @param sizeNow The number of active sessions now
   */

  void onLogin(long sizeNow);

  /**
   * A login session was closed.
   *
   * @param sizeNow The number of active sessions now
   */

  void onLoginClosed(long sizeNow);
}
