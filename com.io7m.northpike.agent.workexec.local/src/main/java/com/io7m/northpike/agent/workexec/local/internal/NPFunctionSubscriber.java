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


package com.io7m.northpike.agent.workexec.local.internal;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Objects;
import java.util.concurrent.Flow;
import java.util.function.Consumer;

/**
 * A perpetual function subscriber.
 *
 * @param <T> The type of received values
 */

final class NPFunctionSubscriber<T> implements Flow.Subscriber<T>
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPFunctionSubscriber.class);

  private final Consumer<T> consumer;

  /**
   * @param inConsumer The consumer of values
   * @param <T>        The type of received values
   *
   * @return A subscriber
   */

  public static <T> Flow.Subscriber<T> createSubscriber(
    final Consumer<T> inConsumer)
  {
    return new NPFunctionSubscriber<>(inConsumer);
  }

  private NPFunctionSubscriber(
    final Consumer<T> inConsumer)
  {
    this.consumer =
      Objects.requireNonNull(inConsumer, "consumer");
  }

  @Override
  public void onSubscribe(
    final Flow.Subscription subscription)
  {
    subscription.request(Long.MAX_VALUE);
  }

  @Override
  public void onNext(
    final T item)
  {
    this.consumer.accept(item);
  }

  @Override
  public void onError(
    final Throwable throwable)
  {
    LOG.debug("", throwable);
  }

  @Override
  public void onComplete()
  {

  }
}
