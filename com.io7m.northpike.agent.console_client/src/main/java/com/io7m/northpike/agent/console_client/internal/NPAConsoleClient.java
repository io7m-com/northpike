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


package com.io7m.northpike.agent.console_client.internal;

import com.io7m.northpike.agent.console_client.api.NPAConsoleClientConfiguration;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientException;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandDisconnect;
import com.io7m.northpike.protocol.agent_console.NPACCommandType;
import com.io7m.northpike.protocol.agent_console.NPACResponseError;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.util.Objects;

/**
 * The default console client.
 */

public final class NPAConsoleClient implements NPAConsoleClientType
{
  private final NPAConsoleClientConfiguration configuration;
  private NPAConsoleConnectionType connection;

  /**
   * The default console client.
   *
   * @param inConfiguration The configuration
   */

  public NPAConsoleClient(
    final NPAConsoleClientConfiguration inConfiguration)
  {
    this.configuration =
      Objects.requireNonNull(inConfiguration, "configuration");
  }

  @Override
  public void login(
    final InetSocketAddress address,
    final String accessKey)
    throws NPAConsoleClientException, InterruptedException
  {
    try {
      this.connection =
        NPAConsoleConnection.open(
          new NPAConsoleConnectionParameters(
            this.configuration,
            accessKey,
            address
          )
        );
    } catch (final NPException e) {
      throw NPAConsoleExceptions.wrap(e);
    } catch (final IOException e) {
      throw NPAConsoleExceptions.errorIO(this.configuration.strings(), e);
    }
  }

  @Override
  public void close()
    throws NPAConsoleClientException
  {
    final var openConnection = this.connection;
    if (openConnection != null) {
      try {
        try {
          openConnection.send(NPACCommandDisconnect.of());
        } catch (final NPException e) {
          throw NPAConsoleExceptions.wrap(e);
        } catch (final InterruptedException e) {
          Thread.currentThread().interrupt();
        }
        openConnection.close();
      } catch (final IOException e) {
        throw NPAConsoleExceptions.errorIO(this.configuration.strings(), e);
      }
    }
  }

  @Override
  public <R extends NPACResponseType> R execute(
    final NPACCommandType<R> command)
    throws NPAConsoleClientException, InterruptedException
  {
    try {
      final var r = this.connection.ask(command);
      return switch (r) {
        case final NPACResponseError error -> {
          throw new NPException(
            error.message(),
            error.errorCode(),
            error.attributes(),
            error.remediatingAction()
          );
        }
        default -> (R) r;
      };
    } catch (final NPException e) {
      throw NPAConsoleExceptions.wrap(e);
    } catch (final IOException e) {
      throw NPAConsoleExceptions.errorIO(this.configuration.strings(), e);
    }
  }

  @Override
  public boolean isClosed()
  {
    if (this.connection instanceof final NPAConsoleConnection c) {
      return c.isClosed();
    }
    return false;
  }

  @Override
  public String description()
  {
    return "Agent console client service.";
  }

  @Override
  public String toString()
  {
    return "[NPAConsoleClient 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
