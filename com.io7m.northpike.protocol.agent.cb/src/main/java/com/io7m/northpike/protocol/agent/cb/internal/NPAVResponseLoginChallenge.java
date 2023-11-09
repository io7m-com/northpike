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


package com.io7m.northpike.protocol.agent.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBByteArray;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.agents.NPAgentLoginChallenge;
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;
import com.io7m.northpike.protocol.agent.cb.NPA1LoginChallenge;
import com.io7m.northpike.protocol.agent.cb.NPA1ResponseLoginChallenge;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import java.nio.ByteBuffer;

/**
 * A validator.
 */

public enum NPAVResponseLoginChallenge
  implements NPProtocolMessageValidatorType<NPAResponseLoginChallenge, NPA1ResponseLoginChallenge>
{
  /**
   * A validator.
   */

  RESPONSE_LOGIN_CHALLENGE;

  @Override
  public NPA1ResponseLoginChallenge convertToWire(
    final NPAResponseLoginChallenge message)
  {
    return new NPA1ResponseLoginChallenge(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      new NPA1LoginChallenge(
        new CBUUID(message.challenge().id()),
        new CBByteArray(ByteBuffer.wrap(message.challenge().data()))
      )
    );
  }

  @Override
  public NPAResponseLoginChallenge convertFromWire(
    final NPA1ResponseLoginChallenge message)
  {
    return new NPAResponseLoginChallenge(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      new NPAgentLoginChallenge(
        message.fieldChallenge().fieldId().value(),
        message.fieldChallenge().fieldValue().value().array()
      )
    );
  }
}
