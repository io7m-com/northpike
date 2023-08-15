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

import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.model.NPException;

import java.io.IOException;
import java.util.Optional;

/**
 * The type of synchronous, blocking message connections.
 *
 * @param <M> The type of messages
 * @param <R> The type of messages that are responses
 */

public interface NPMessageConnectionType<M, R extends M>
  extends CloseableType
{
  /**
   * Send a message and block until the message is written to the underlying
   * network transport.
   *
   * @param message The message
   *
   * @throws NPException          On errors
   * @throws InterruptedException On interruption
   * @throws IOException          On errors
   */

  void send(M message)
    throws NPException, InterruptedException, IOException;

  /**
   * Send a message and wait until the response to that message comes back,
   * and return the response.
   *
   * @param message The message
   *
   * @return The response
   *
   * @throws NPException          On errors
   * @throws InterruptedException On interruption
   * @throws IOException          On errors
   */

  R ask(M message)
    throws NPException, InterruptedException, IOException;

  /**
   * Retrieve a message if one is available. The method will block until
   * the underlying network transport indicates that a message is available.
   *
   * @return The message, if any
   *
   * @throws NPException          On errors
   * @throws InterruptedException On interruption
   * @throws IOException          On errors
   */

  Optional<M> read()
    throws NPException, InterruptedException, IOException;

  @Override
  void close()
    throws IOException;
}
