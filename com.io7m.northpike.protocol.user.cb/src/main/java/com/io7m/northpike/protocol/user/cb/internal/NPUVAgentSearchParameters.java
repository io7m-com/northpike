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

import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.model.agents.NPAgentSearchParameters;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AgentSearchParameters;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVStrings.STRINGS;

/**
 * A validator.
 */

public enum NPUVAgentSearchParameters
  implements NPProtocolMessageValidatorType<NPAgentSearchParameters, NPU1AgentSearchParameters>
{
  /**
   * A validator.
   */

  AGENT_SEARCH_PARAMETERS;

  private static final NPUVComparisonsSet<String, CBString> SET_VALIDATOR =
    new NPUVComparisonsSet<>(STRINGS);

  @Override
  public NPU1AgentSearchParameters convertToWire(
    final NPAgentSearchParameters message)
    throws NPProtocolException
  {
    return new NPU1AgentSearchParameters(
      SET_VALIDATOR.convertToWire(
        message.matchLabels().map(NPAgentLabelName::toString)
      ),
      unsigned32(message.pageSize())
    );
  }

  @Override
  public NPAgentSearchParameters convertFromWire(
    final NPU1AgentSearchParameters message)
    throws NPProtocolException
  {
    return new NPAgentSearchParameters(
      SET_VALIDATOR.convertFromWire(message.fieldMatchLabels())
        .map(NPAgentLabelName::of),
      false,
      message.fieldPageSize().value()
    );
  }
}
