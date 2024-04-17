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
import com.io7m.northpike.telemetry.api.NPEventSeverity;

import java.net.InetAddress;
import java.util.Map;
import java.util.Optional;
import java.util.UUID;

/**
 * A user disconnected.
 *
 * @param address The remote address
 * @param port    The remote port
 * @param userID  The user ID (if available)
 */

@NPDocumentation("A user disconnected.")
public record NPUserDisconnected(
  InetAddress address,
  int port,
  Optional<UUID> userID)
  implements NPUserEventType
{
  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.INFO;
  }

  @Override
  public String name()
  {
    return "UserDisconnected";
  }

  @Override
  public String message()
  {
    return "Disconnected";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("RemoteAddress", this.address.toString()),
      Map.entry("RemotePort", Integer.toUnsignedString(this.port)),
      Map.entry(
        "UserID",
        this.userID.map(UUID::toString).orElse(""))
    );
  }
}
