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
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandAgentSearchBegin;
import com.io7m.northpike.protocol.user.cb.NPU1CommandAgentSearchBegin;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVAgentSearchParameters.AGENT_SEARCH_PARAMETERS;

/**
 * A validator.
 */

public enum NPUVCommandAgentSearchBegin
  implements NPProtocolMessageValidatorType<NPUCommandAgentSearchBegin, NPU1CommandAgentSearchBegin>
{
  /**
   * A validator.
   */

  COMMAND_AGENT_SEARCH_BEGIN;

  @Override
  public NPU1CommandAgentSearchBegin convertToWire(
    final NPUCommandAgentSearchBegin message)
    throws NPProtocolException
  {
    return new NPU1CommandAgentSearchBegin(
      new CBUUID(message.messageID()),
      AGENT_SEARCH_PARAMETERS.convertToWire(message.parameters())
    );
  }

  @Override
  public NPUCommandAgentSearchBegin convertFromWire(
    final NPU1CommandAgentSearchBegin message)
    throws NPProtocolException
  {
    return new NPUCommandAgentSearchBegin(
      message.fieldMessageId().value(),
      AGENT_SEARCH_PARAMETERS.convertFromWire(message.fieldParameters())
    );
  }
}
