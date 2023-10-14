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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUResponseAgentGet;
import com.io7m.northpike.protocol.user.cb.NPU1ResponseAgentGet;

import java.util.Optional;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVAgentDescription.AGENT_DESCRIPTION;

/**
 * A validator.
 */

public enum NPUVResponseAgentGet
  implements NPProtocolMessageValidatorType<NPUResponseAgentGet, NPU1ResponseAgentGet>
{
  /**
   * A validator.
   */

  RESPONSE_AGENT_GET;

  @Override
  public NPU1ResponseAgentGet convertToWire(
    final NPUResponseAgentGet message)
  {
    return new NPU1ResponseAgentGet(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBOptionType.fromOptional(
        message.agent()
          .map(AGENT_DESCRIPTION::convertToWire)
      )
    );
  }

  @Override
  public NPUResponseAgentGet convertFromWire(
    final NPU1ResponseAgentGet message)
    throws NPProtocolException
  {
    final var opt =
      message.fieldDescription().asOptional();

    final Optional<NPAgentDescription> agentOpt;
    if (opt.isPresent()) {
      agentOpt = Optional.of(AGENT_DESCRIPTION.convertFromWire(opt.get()));
    } else {
      agentOpt = Optional.empty();
    }

    return new NPUResponseAgentGet(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      agentOpt
    );
  }
}
