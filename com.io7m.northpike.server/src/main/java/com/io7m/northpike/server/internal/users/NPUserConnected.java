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

package com.io7m.northpike.server.internal.users;

import com.io7m.northpike.model.NPDocumentation;
import com.io7m.northpike.server.internal.agents.NPAgentEventType;
import com.io7m.northpike.telemetry.api.NPEventSeverity;

import java.net.InetAddress;
import java.util.Map;

/**
 * A user connected successfully.
 *
 * @param address The remote address
 * @param port    The remote port
 */

@NPDocumentation("A user connected successfully.")
public record NPUserConnected(
  InetAddress address,
  int port)
  implements NPAgentEventType
{
  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.INFO;
  }

  @Override
  public String name()
  {
    return "UserConnected";
  }

  @Override
  public String message()
  {
    return "Connected";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("RemoteAddress", this.address.toString()),
      Map.entry("RemotePort", Integer.toUnsignedString(this.port))
    );
  }
}
