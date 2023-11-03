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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.model.agents.NPAgentServerSummary;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1AgentServerSummary;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVAgentServerSummary
  implements NPProtocolMessageValidatorType<NPAgentServerSummary, NPAC1AgentServerSummary>
{
  /**
   * A validator.
   */

  AGENT_SERVER_SUMMARY;

  @Override
  public NPAC1AgentServerSummary convertToWire(
    final NPAgentServerSummary message)
  {
    return new NPAC1AgentServerSummary(
      new CBUUID(message.id().value()),
      string(message.hostname())
    );
  }

  @Override
  public NPAgentServerSummary convertFromWire(
    final NPAC1AgentServerSummary message)
  {
    return new NPAgentServerSummary(
      new NPAgentServerID(message.fieldId().value()),
      message.fieldHostName().value()
    );
  }
}
