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


package com.io7m.northpike.user_client.internal;

import com.io7m.idstore.model.IdName;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandType;
import com.io7m.northpike.protocol.user.NPUResponseType;
import com.io7m.northpike.tls.NPTLSConfigurationType;
import com.io7m.northpike.user_client.api.NPUserClientConfiguration;
import com.io7m.northpike.user_client.api.NPUserClientException;
import com.io7m.northpike.user_client.api.NPUserClientType;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.util.Objects;

/**
 * The default user client implementation.
 */

public final class NPUserClient implements NPUserClientType
{
  private final NPUserClientConfiguration configuration;
  private NPUserConnectionType connection;

  /**
   * The default user client implementation.
   *
   * @param inConfiguration The client configuration
   */

  public NPUserClient(
    final NPUserClientConfiguration inConfiguration)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
  }

  @Override
  public void login(
    final InetSocketAddress address,
    final NPTLSConfigurationType tls,
    final IdName name,
    final String password)
    throws NPUserClientException, InterruptedException
  {
    try {
      this.connection =
        NPUserConnection.open(
          new NPUserConnectionParameters(
            this.configuration,
            name,
            password,
            address,
            tls
          )
        );
    } catch (final NPException e) {
      throw NPUserExceptions.wrap(e);
    } catch (final IOException e) {
      throw NPUserExceptions.errorIO(this.configuration.strings(), e);
    }
  }

  @Override
  public void close()
    throws NPUserClientException
  {
    final var openConnection = this.connection;
    if (openConnection != null) {
      try {
        try {
          openConnection.send(NPUCommandDisconnect.of());
        } catch (final NPException e) {
          throw NPUserExceptions.wrap(e);
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
        }
        openConnection.close();
      } catch (final IOException e) {
        throw NPUserExceptions.errorIO(this.configuration.strings(), e);
      }
    }
  }

  @Override
  public <R extends NPUResponseType> R execute(
    final NPUCommandType<R> command)
    throws NPUserClientException, InterruptedException
  {
    try {
      return (R) this.connection.ask(command);
    } catch (final NPException e) {
      throw NPUserExceptions.wrap(e);
    } catch (final IOException e) {
      throw NPUserExceptions.errorIO(this.configuration.strings(), e);
    }
  }

  @Override
  public boolean isClosed()
  {
    if (this.connection instanceof final NPUserConnection c) {
      return c.isClosed();
    }
    return false;
  }
}
