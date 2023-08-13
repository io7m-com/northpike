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

import com.io7m.jaffirm.core.Preconditions;

import java.util.Map;
import java.util.Objects;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

/**
 * A simple message correlator.
 *
 * @param <M> The type of messages to be sent
 * @param <R> The type of response messages
 */

public final class NPMessageCorrelator<M, R>
  implements NPMessageCorrelatorType<M, R>
{
  private final Function<M, UUID> messageId;
  private final Function<R, UUID> correlationId;
  private final Map<UUID, CompletableFuture<R>> awaitingResponses;

  /**
   * A simple message correlator.
   *
   * @param inMessageId     A function that, given a message, returns an ID
   * @param inCorrelationId A function that, given a response, returns the ID of the original message
   */

  public NPMessageCorrelator(
    final Function<M, UUID> inMessageId,
    final Function<R, UUID> inCorrelationId)
  {
    this.messageId =
      Objects.requireNonNull(inMessageId, "messageId");
    this.correlationId =
      Objects.requireNonNull(inCorrelationId, "correlationId");
    this.awaitingResponses =
      new ConcurrentHashMap<>(32);
  }

  @Override
  public CompletableFuture<? extends R> onSend(
    final M message)
  {
    Objects.requireNonNull(message, "message");

    final var id =
      this.messageId.apply(message);

    Preconditions.checkPreconditionV(
      !this.awaitingResponses.containsKey(id),
      "Sent messages must not contain ID %s",
      id
    );

    final CompletableFuture<R> future =
      new CompletableFuture<>();

    this.awaitingResponses.put(id, future);
    return future;
  }

  @Override
  public <Q extends R> boolean onReceive(
    final Q response)
  {
    Objects.requireNonNull(response, "response");

    final var id =
      this.correlationId.apply(response);
    final var future =
      this.awaitingResponses.remove(id);

    if (future != null) {
      future.complete(response);
      return true;
    }
    return false;
  }

  @Override
  public void close()
  {
    for (final var f : this.awaitingResponses.values()) {
      f.cancel(true);
    }
    this.awaitingResponses.clear();
  }
}
