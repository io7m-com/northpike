/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.connections;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.time.Duration;
import java.util.Objects;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.TimeUnit;

/**
 * A timeout watchdog that interrupts a given thread if the watchdog has
 * not been cancelled before a given duration elapses.
 */

public final class NPTimeout
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPTimeout.class);

  private final Thread target;
  private final Duration time;
  private final ArrayBlockingQueue<Integer> queue;

  private NPTimeout(
    final Thread inTarget,
    final Duration inTime)
  {
    this.target =
      Objects.requireNonNull(inTarget, "inTarget");
    this.time =
      Objects.requireNonNull(inTime, "inTime");
    this.queue =
      new ArrayBlockingQueue<>(1);
  }

  /**
   * Create a new watchdog.
   *
   * @param target The thread that will be interrupted
   * @param time   The maximum elapsed time
   *
   * @return A new watchdog
   */

  public static NPTimeout create(
    final Thread target,
    final Duration time)
  {
    final var timeout = new NPTimeout(target, time);

    Thread.ofVirtual()
      .start(() -> {
        try {
          LOG.trace("Timeout watchdog started: {}", timeout.time);

          final var r =
            timeout.queue.poll(timeout.time.toMillis(), TimeUnit.MILLISECONDS);

          if (r == null) {
            LOG.trace("Timeout watchdog timed out.");
            timeout.target.interrupt();
          } else {
            LOG.trace("Timeout watchdog cancelled.");
          }
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
          LOG.trace("Timeout watchdog interrupted.");
        }
      });

    return timeout;
  }

  /**
   * Cancel the watchdog.
   */

  public void cancel()
  {
    this.queue.add(Integer.valueOf(0));
  }
}
