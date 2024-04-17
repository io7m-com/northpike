/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.model.agents;

import java.net.InetSocketAddress;
import java.time.Duration;
import java.util.Objects;

/**
 * Information about an agent connection.
 *
 * @param agentID The agent ID
 * @param address The remote agent address
 * @param latency The remote agent latency
 */

public record NPAgentConnected(
  NPAgentID agentID,
  InetSocketAddress address,
  Duration latency)
{
  /**
   * Information about an agent connection.
   *
   * @param agentID The agent ID
   * @param address The remote agent address
   * @param latency The remote agent latency
   */

  public NPAgentConnected
  {
    Objects.requireNonNull(agentID, "agentID");
    Objects.requireNonNull(address, "address");
    Objects.requireNonNull(latency, "latency");

    if (address.isUnresolved()) {
      throw new IllegalArgumentException("Agent addresses must be resolved.");
    }
  }
}
