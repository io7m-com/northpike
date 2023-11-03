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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1ResponseAgent;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import java.util.Optional;

import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVAgentDescription.AGENT_DESCRIPTION;

/**
 * A validator.
 */

public enum NPACVResponseAgent
  implements NPProtocolMessageValidatorType<NPACResponseAgent, NPAC1ResponseAgent>
{
  /**
   * A validator.
   */

  RESPONSE_AGENT;

  @Override
  public NPAC1ResponseAgent convertToWire(
    final NPACResponseAgent message)
  {
    return new NPAC1ResponseAgent(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBOptionType.fromOptional(
        message.results()
          .map(AGENT_DESCRIPTION::convertToWire)
      )
    );
  }

  @Override
  public NPACResponseAgent convertFromWire(
    final NPAC1ResponseAgent message)
    throws NPProtocolException
  {
    final Optional<NPACResponseAgent.Result> agent;
    final var agentOpt =
      message.fieldAgent().asOptional();
    if (agentOpt.isPresent()) {
      agent = Optional.of(AGENT_DESCRIPTION.convertFromWire(agentOpt.get()));
    } else {
      agent = Optional.empty();
    }

    return new NPACResponseAgent(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      agent
    );
  }
}
