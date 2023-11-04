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

import com.io7m.cedarbridge.runtime.api.CBCore;
import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.protocol.agent_console.NPACResponseError;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1ResponseError;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVResponseError
  implements NPProtocolMessageValidatorType<NPACResponseError, NPAC1ResponseError>
{
  /**
   * A validator.
   */

  RESPONSE_ERROR;

  @Override
  public NPAC1ResponseError convertToWire(
    final NPACResponseError message)
  {
    return new NPAC1ResponseError(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      string(message.errorCode().id()),
      string(message.message()),
      CBMaps.ofMapString(message.attributes()),
      CBOptionType.fromOptional(message.remediatingAction().map(CBCore::string))
    );
  }

  @Override
  public NPACResponseError convertFromWire(
    final NPAC1ResponseError message)
  {
    return new NPACResponseError(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      new NPErrorCode(message.fieldErrorCode().value()),
      message.fieldMessage().value(),
      CBMaps.toMapString(message.fieldAttributes()),
      message.fieldRemediatingAction()
        .asOptional()
        .map(CBString::value)
    );
  }
}
