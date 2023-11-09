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

package com.io7m.northpike.agent.console_client.api;

import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.protocol.agent_console.NPACCommandType;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;
import com.io7m.repetoir.core.RPServiceType;

import java.net.InetSocketAddress;

/**
 * A console client.
 */

public interface NPAConsoleClientType extends CloseableType, RPServiceType
{
  /**
   * Log in to the given agent.
   *
   * @param address   The address
   * @param accessKey The access key
   *
   * @throws NPAConsoleClientException On errors
   * @throws InterruptedException      On interruption
   */

  void login(
    InetSocketAddress address,
    String accessKey)
    throws NPAConsoleClientException, InterruptedException;

  @Override
  void close()
    throws NPAConsoleClientException;

  /**
   * Execute the given command.
   *
   * @param command The command
   * @param <R>     The type of responses
   *
   * @return The response, on success
   *
   * @throws NPAConsoleClientException On errors
   * @throws InterruptedException      On interruption
   */

  <R extends NPACResponseType> R execute(
    NPACCommandType<R> command)
    throws NPAConsoleClientException, InterruptedException;
}
