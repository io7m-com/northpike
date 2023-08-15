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

import com.io7m.northpike.model.NPException;

import java.io.IOException;
import java.util.LinkedList;
import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

/**
 * An abstract implementation of the message connection interface.
 *
 * @param <M> The type of messages
 * @param <R> The subset of messages that are responses
 */

public abstract class NPMessageConnectionAbstract<M, R extends M>
  implements NPMessageConnectionType<M, R>
{
  private final NPMessageConnectionHandlerType<M> handler;
  private final LinkedList<M> received;

  protected NPMessageConnectionAbstract(
    final NPMessageConnectionHandlerType<M> inHandler)
  {
    this.handler =
      Objects.requireNonNull(inHandler, "handler");
    this.received =
      new LinkedList<>();
  }

  /**
   * Determine if a message is a response.
   *
   * @param message The message
   *
   * @return The message as a value of {@code R}, or null if the message is
   * not a response
   */

  protected abstract R isResponse(
    M message);

  /**
   * @param message The message
   *
   * @return The ID of the message
   */

  protected abstract UUID messageID(
    M message);

  /**
   * @param message The message
   *
   * @return The correlation ID of the message (the ID of the message to
   * which this response is a response)
   */

  protected abstract UUID correlationID(
    R message);

  @Override
  public final void send(
    final M message)
    throws NPException, IOException
  {
    this.handler.send(message);
  }

  @Override
  public final R ask(
    final M message)
    throws NPException, InterruptedException, IOException
  {
    final var id = this.messageID(message);
    this.handler.send(message);

    while (!Thread.interrupted()) {
      final var responseOpt = this.handler.receive();
      if (responseOpt.isPresent()) {
        final var response = responseOpt.get();
        final var actual = this.isResponse(response);
        if (actual != null) {
          if (Objects.equals(this.correlationID(actual), id)) {
            return actual;
          }
        }
        this.received.add(response);
      }
    }

    throw new InterruptedException();
  }

  @Override
  public final Optional<M> read()
    throws NPException, IOException
  {
    final var m = this.received.poll();
    if (m != null) {
      return Optional.of(m);
    }
    return this.handler.receive();
  }

  @Override
  public final void close()
    throws IOException
  {
    this.handler.close();
  }

  @Override
  public final boolean isClosed()
  {
    return this.handler.isClosed();
  }
}
