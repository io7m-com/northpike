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


package com.io7m.northpike.agent.internal;

import com.io7m.jattribute.core.AttributeReadableType;
import com.io7m.northpike.agent.api.NPAgentConnectionStatus;
import com.io7m.northpike.agent.api.NPAgentException;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAEventType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseType;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Flow;

/**
 * A connection to a server, exposing asynchronous I/O operations and
 * providing transparent authentication and re-connection in the case of
 * connection failures.
 */

public interface NPAgentConnectionType extends AutoCloseable
{
  /**
   * @return The status of the connection
   */

  AttributeReadableType<NPAgentConnectionStatus> status();

  /**
   * Submit a command. The returned future is completed when an appropriate
   * response is returned by the server.
   *
   * @param command The command
   * @param <R>     The type of responses
   *
   * @return The operation in progress
   */

  <R extends NPAResponseType> CompletableFuture<R> submitCommand(
    NPACommandType<R> command);

  /**
   * Submit a response. The returned future is completed as soon as the message
   * is written to the underlying network transport.
   *
   * @param response The response
   *
   * @return The operation in progress
   */

  CompletableFuture<Void> submitResponse(
    NPAResponseType response);

  /**
   * Submit an event. The returned future is completed as soon as the message
   * is written to the underlying network transport.
   *
   * @param event The event
   *
   * @return The operation in progress
   */

  CompletableFuture<Void> submitEvent(
    NPAEventType event);

  /**
   * Receive messages.
   *
   * @return The messages received since the last call to {{@link #takeReceivedMessages()}}
   */

  List<NPAMessageType> takeReceivedMessages();

  /**
   * @return A stream of events produced by the connection
   */

  Flow.Publisher<NPAgentException> exceptions();

  @Override
  void close()
    throws NPAgentException;
}
