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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecSupported;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1CommandWorkExecSupported;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

/**
 * A validator.
 */

public enum NPACVCommandWorkExecSupported
  implements NPProtocolMessageValidatorType<NPACCommandWorkExecSupported, NPAC1CommandWorkExecSupported>
{
  /**
   * A validator.
   */

  COMMAND_WORK_EXEC_SUPPORTED;

  @Override
  public NPAC1CommandWorkExecSupported convertToWire(
    final NPACCommandWorkExecSupported message)
  {
    return new NPAC1CommandWorkExecSupported(
      new CBUUID(message.messageID())
    );
  }

  @Override
  public NPACCommandWorkExecSupported convertFromWire(
    final NPAC1CommandWorkExecSupported message)
  {
    return new NPACCommandWorkExecSupported(
      message.fieldMessageId().value()
    );
  }
}
