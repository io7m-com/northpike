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

import java.util.List;
import java.util.Optional;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Flow;

/**
 * A connection between two peers, exposing asynchronous I/O operations and
 * providing transparent re-connection in the case of connection failures.
 *
 * @param <M> The type of messages
 * @param <R> The type of responses
 */

public interface NPMessageConnectionType<M, R extends M>
  extends AutoCloseable
{
  /**
   * Submit a message that expects a response. The returned future is completed
   * when an appropriate response is returned from the peer.
   *
   * @param message The message
   *
   * @return The operation in progress
   */

  CompletableFuture<R> submitExpectingResponse(M message);

  /**
   * Submit a message that does not expect a response. The method blocks
   * until the message is written to the network transport.
   *
   * @param message The message
   */

  void submitExpectingNoResponse(M message);

  /**
   * Receive messages.
   *
   * @return The messages received since the last call to {{@link #takeReceivedMessages()}}
   */

  List<M> takeReceivedMessages();

  /**
   * Peek at the most recently received message.
   *
   * @return The messages received since the last call to {{@link #takeReceivedMessages()}}
   */

  Optional<M> peekReceivedMessage();

  /**
   * Take the most recently received message.
   *
   * @return The messages received since the last call to {{@link #takeReceivedMessages()}}
   */

  Optional<M> takeReceivedMessage();

  /**
   * @return A stream of events produced by the connection
   */

  Flow.Publisher<NPException> exceptions();

  @Override
  void close()
    throws NPException;
}
