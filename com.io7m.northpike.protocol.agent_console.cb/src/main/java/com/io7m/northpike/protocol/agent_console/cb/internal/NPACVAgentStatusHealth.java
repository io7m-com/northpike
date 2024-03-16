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


package com.io7m.northpike.protocol.agent_console.cb.internal;

import com.io7m.northpike.model.agents.NPAgentStatusHealth;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1AgentStatusHealth;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.model.agents.NPAgentStatusHealth.HEALTHY;
import static com.io7m.northpike.model.agents.NPAgentStatusHealth.UNHEALTHY;

/**
 * A validator.
 */

public enum NPACVAgentStatusHealth
  implements NPProtocolMessageValidatorType<
  NPAgentStatusHealth, NPAC1AgentStatusHealth>
{
  /**
   * A validator.
   */

  AGENT_STATUS_HEALTH;

  @Override
  public NPAC1AgentStatusHealth convertToWire(
    final NPAgentStatusHealth message)
  {
    return switch (message) {
      case HEALTHY -> new NPAC1AgentStatusHealth.Healthy();
      case UNHEALTHY -> new NPAC1AgentStatusHealth.Unhealthy();
    };
  }

  @Override
  public NPAgentStatusHealth convertFromWire(
    final NPAC1AgentStatusHealth message)
  {
    return switch (message) {
      case final NPAC1AgentStatusHealth.Healthy healthy -> HEALTHY;
      case final NPAC1AgentStatusHealth.Unhealthy unhealthy -> UNHEALTHY;
    };
  }
}
