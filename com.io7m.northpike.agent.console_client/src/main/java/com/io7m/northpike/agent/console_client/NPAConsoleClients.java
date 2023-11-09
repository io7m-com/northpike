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


package com.io7m.northpike.agent.console_client;

import com.io7m.northpike.agent.console_client.api.NPAConsoleClientConfiguration;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientFactoryType;
import com.io7m.northpike.agent.console_client.api.NPAConsoleClientType;
import com.io7m.northpike.agent.console_client.internal.NPAConsoleClient;

/**
 * The factory of agent console clients.
 */

public final class NPAConsoleClients implements NPAConsoleClientFactoryType
{
  /**
   * The factory of agent console clients.
   */

  public NPAConsoleClients()
  {

  }

  @Override
  public NPAConsoleClientType createConsoleClient(
    final NPAConsoleClientConfiguration configuration)
  {
    return new NPAConsoleClient(configuration);
  }

  @Override
  public String description()
  {
    return "Agent console client service.";
  }

  @Override
  public String toString()
  {
    return "[NPAConsoleClients 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }
}
