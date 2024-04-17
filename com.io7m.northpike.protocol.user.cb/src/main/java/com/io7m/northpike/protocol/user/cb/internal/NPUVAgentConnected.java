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


package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.agents.NPAgentConnected;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AgentConnected;

import java.net.InetSocketAddress;
import java.time.Duration;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned16;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned64;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVIPAddress.IP_ADDRESS;

/**
 * A validator.
 */

public enum NPUVAgentConnected
  implements NPProtocolMessageValidatorType<NPAgentConnected, NPU1AgentConnected>
{
  /**
   * A validator.
   */

  AGENT_CONNECTED;

  @Override
  public NPU1AgentConnected convertToWire(
    final NPAgentConnected message)
  {
    return new NPU1AgentConnected(
      new CBUUID(message.agentID().value()),
      IP_ADDRESS.convertToWire(message.address().getAddress()),
      unsigned16(message.address().getPort()),
      unsigned64(message.latency().toMillis())
    );
  }

  @Override
  public NPAgentConnected convertFromWire(
    final NPU1AgentConnected message)
  {
    return new NPAgentConnected(
      new NPAgentID(message.fieldId().value()),
      new InetSocketAddress(
        IP_ADDRESS.convertFromWire(message.fieldRemoteAddress()),
        message.fieldRemotePort().value()
      ),
      Duration.ofMillis(message.fieldLatencyMilliseconds().value())
    );
  }
}
