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
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchNext;
import com.io7m.northpike.protocol.user.cb.NPU1CommandPlanSearchNext;

/**
 * A validator.
 */

public enum NPUVCommandPlanSearchNext
  implements NPProtocolMessageValidatorType<
  NPUCommandPlanSearchNext,
  NPU1CommandPlanSearchNext>
{
  /**
   * A validator.
   */

  COMMAND_PLAN_SEARCH_NEXT;

  @Override
  public NPU1CommandPlanSearchNext convertToWire(
    final NPUCommandPlanSearchNext message)
  {
    return new NPU1CommandPlanSearchNext(
      new CBUUID(message.messageID())
    );
  }

  @Override
  public NPUCommandPlanSearchNext convertFromWire(
    final NPU1CommandPlanSearchNext message)
  {
    return new NPUCommandPlanSearchNext(
      message.fieldMessageId().value()
    );
  }
}
