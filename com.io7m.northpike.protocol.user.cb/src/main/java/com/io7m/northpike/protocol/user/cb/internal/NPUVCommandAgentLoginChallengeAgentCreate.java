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
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandAgentLoginChallengeAgentCreate;
import com.io7m.northpike.protocol.user.cb.NPU1CommandAgentLoginChallengeAgentCreate;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVCommandAgentLoginChallengeAgentCreate
  implements NPProtocolMessageValidatorType<
  NPUCommandAgentLoginChallengeAgentCreate,
    NPU1CommandAgentLoginChallengeAgentCreate>
{
  /**
   * A validator.
   */

  COMMAND_AGENT_LOGIN_CHALLENGE_AGENT_CREATE;

  @Override
  public NPU1CommandAgentLoginChallengeAgentCreate convertToWire(
    final NPUCommandAgentLoginChallengeAgentCreate message)
  {
    return new NPU1CommandAgentLoginChallengeAgentCreate(
      new CBUUID(message.messageID()),
      new CBUUID(message.loginChallenge()),
      new CBUUID(message.agent().value()),
      string(message.name())
    );
  }

  @Override
  public NPUCommandAgentLoginChallengeAgentCreate convertFromWire(
    final NPU1CommandAgentLoginChallengeAgentCreate message)
  {
    return new NPUCommandAgentLoginChallengeAgentCreate(
      message.fieldMessageId().value(),
      message.fieldChallenge().value(),
      new NPAgentID(message.fieldAgentId().value()),
      message.fieldAgentName().value()
    );
  }
}
