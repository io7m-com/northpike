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

package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.model.NPDocumentation;
import com.io7m.northpike.model.agents.NPAgentKeyID;
import com.io7m.northpike.telemetry.api.NPEventSeverity;

import java.net.InetAddress;
import java.util.Map;
import java.util.Optional;

/**
 * An agent failed to authenticate.
 *
 * @param address The remote address
 * @param port    The remote port
 * @param reason  The reason
 * @param keyID   The key ID of the agent, if any
 */

@NPDocumentation("An agent failed to authenticate.")
public record NPAgentAuthenticationFailed(
  InetAddress address,
  int port,
  Optional<NPAgentKeyID> keyID,
  String reason)
  implements NPAgentEventType
{
  @Override
  public NPEventSeverity severity()
  {
    return NPEventSeverity.ERROR;
  }

  @Override
  public String name()
  {
    return "AgentAuthenticationFailed";
  }

  @Override
  public String message()
  {
    return "AgentAuthenticationFailed";
  }

  @Override
  public Map<String, String> asAttributes()
  {
    return Map.ofEntries(
      Map.entry("RemoteAddress", this.address.toString()),
      Map.entry("RemotePort", Integer.toUnsignedString(this.port)),
      Map.entry("KeyID", this.keyID.map(NPAgentKeyID::toString).orElse("")),
      Map.entry("Reason", this.reason)
    );
  }
}
