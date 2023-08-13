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

package com.io7m.northpike.connections;

import java.util.concurrent.CompletableFuture;

/**
 * <p>
 * A message correlator interface.
 * </p>
 * <p>
 * A message correlator accepts notifications that messages have been sent,
 * and notifications that messages have been received. It correlates received
 * responses with the original sent messages.
 * </p>
 *
 * @param <M> The type of messages to be sent
 * @param <R> The type of responses
 */

public interface NPMessageCorrelatorType<M, R>
  extends AutoCloseable
{
  /**
   * Notify the connections that a message has been sent.
   *
   * @param message The message
   *
   * @return A future that will be completed when a correlated response has
   * been received
   */

  CompletableFuture<? extends R> onSend(M message);

  /**
   * Notify the connections that a response has been received.
   *
   * @param response The response
   * @param <Q>      The type of response
   *
   * @return {@code true} if the given message was correlated to a message
   */

  <Q extends R> boolean onReceive(Q response);

  @Override
  void close();
}
