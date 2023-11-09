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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.protocol.agent_console.NPACResponseWorkExec;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1ResponseWorkExec;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVWorkExecutor.WORK_EXECUTOR;

/**
 * A validator.
 */

public enum NPACVResponseWorkExec
  implements NPProtocolMessageValidatorType<NPACResponseWorkExec, NPAC1ResponseWorkExec>
{
  /**
   * A validator.
   */

  RESPONSE_WORK_EXEC;

  @Override
  public NPAC1ResponseWorkExec convertToWire(
    final NPACResponseWorkExec message)
  {
    return new NPAC1ResponseWorkExec(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBOptionType.fromOptional(
        message.results()
          .map(WORK_EXECUTOR::convertToWire)
      )
    );
  }

  @Override
  public NPACResponseWorkExec convertFromWire(
    final NPAC1ResponseWorkExec message)
  {
    return new NPACResponseWorkExec(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      message.fieldWorkExec()
        .asOptional()
        .map(WORK_EXECUTOR::convertFromWire)
    );
  }
}
