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

import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.northpike.model.agents.NPAgentLoginChallengeRecord;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AgentLoginChallengeRecord;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVAgentLoginChallenge.AGENT_LOGIN_CHALLENGE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVAgentPublicKey.PUBLIC_KEY;

/**
 * A validator.
 */

public enum NPUVAgentLoginChallengeRecord
  implements NPProtocolMessageValidatorType<
  NPAgentLoginChallengeRecord, NPU1AgentLoginChallengeRecord>
{
  /**
   * A validator.
   */

  AGENT_LOGIN_CHALLENGE_RECORD;

  @Override
  public NPU1AgentLoginChallengeRecord convertToWire(
    final NPAgentLoginChallengeRecord message)
    throws NPProtocolException
  {
    return new NPU1AgentLoginChallengeRecord(
      new CBOffsetDateTime(message.timeCreated()),
      string(message.sourceAddress()),
      PUBLIC_KEY.convertToWire(message.key()),
      AGENT_LOGIN_CHALLENGE.convertToWire(message.challenge())
    );
  }

  @Override
  public NPAgentLoginChallengeRecord convertFromWire(
    final NPU1AgentLoginChallengeRecord message)
    throws NPProtocolException
  {
    return new NPAgentLoginChallengeRecord(
      message.fieldTimeCreated().value(),
      message.fieldSourceAddress().value(),
      PUBLIC_KEY.convertFromWire(message.fieldKey()),
      AGENT_LOGIN_CHALLENGE.convertFromWire(message.fieldChallenge())
    );
  }
}
