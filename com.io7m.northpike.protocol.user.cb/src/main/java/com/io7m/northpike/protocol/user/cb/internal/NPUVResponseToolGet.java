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
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUResponseToolGet;
import com.io7m.northpike.protocol.user.cb.NPU1ResponseToolGet;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVToolDescription.TOOL_DESCRIPTION;

/**
 * A validator.
 */

public enum NPUVResponseToolGet
  implements NPProtocolMessageValidatorType<
  NPUResponseToolGet,
  NPU1ResponseToolGet>
{
  /**
   * A validator.
   */

  RESPONSE_TOOL_GET;

  @Override
  public NPU1ResponseToolGet convertToWire(
    final NPUResponseToolGet message)
  {
    return new NPU1ResponseToolGet(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBOptionType.fromOptional(
        message.description().map(TOOL_DESCRIPTION::convertToWire)
      )
    );
  }

  @Override
  public NPUResponseToolGet convertFromWire(
    final NPU1ResponseToolGet message)
  {
    return new NPUResponseToolGet(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      message.fieldDescription()
        .asOptional()
        .map(TOOL_DESCRIPTION::convertFromWire)
    );
  }
}
