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

package com.io7m.northpike.user_client.api;

import com.io7m.idstore.model.IdName;
import com.io7m.jmulticlose.core.CloseableType;
import com.io7m.northpike.protocol.user.NPUCommandType;
import com.io7m.northpike.protocol.user.NPUResponseType;
import com.io7m.northpike.tls.NPTLSConfigurationType;
import com.io7m.repetoir.core.RPServiceType;

import java.net.InetSocketAddress;

/**
 * A user client.
 */

public interface NPUserClientType extends CloseableType, RPServiceType
{
  /**
   * Log in to the given server.
   *
   * @param address  The address
   * @param tls      The TLS configuration
   * @param name     The username
   * @param password The password
   *
   * @throws NPUserClientException On errors
   * @throws InterruptedException  On interruption
   */

  void login(
    InetSocketAddress address,
    NPTLSConfigurationType tls,
    IdName name,
    String password)
    throws NPUserClientException, InterruptedException;

  @Override
  void close()
    throws NPUserClientException;

  /**
   * Execute the given command.
   *
   * @param command The command
   * @param <R>     The type of responses
   *
   * @return The response, on success
   *
   * @throws NPUserClientException On errors
   * @throws InterruptedException  On interruption
   */

  <R extends NPUResponseType> R execute(
    NPUCommandType<R> command)
    throws NPUserClientException, InterruptedException;
}
