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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.protocol.agent.cb.NPA1ResponseLatencyCheck;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

/**
 * A validator.
 */

public enum NPAVResponseSLatencyCheck
  implements NPProtocolMessageValidatorType<NPAResponseLatencyCheck, NPA1ResponseLatencyCheck>
{
  /**
   * A validator.
   */

  RESPONSE_LATENCY_CHECK;

  @Override
  public NPA1ResponseLatencyCheck convertToWire(
    final NPAResponseLatencyCheck message)
  {
    return new NPA1ResponseLatencyCheck(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      new CBOffsetDateTime(message.timeOriginal()),
      new CBOffsetDateTime(message.timeClient())
    );
  }

  @Override
  public NPAResponseLatencyCheck convertFromWire(
    final NPA1ResponseLatencyCheck message)
  {
    return new NPAResponseLatencyCheck(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      message.fieldTimeOriginal().value(),
      message.fieldTimeClient().value()
    );
  }
}
