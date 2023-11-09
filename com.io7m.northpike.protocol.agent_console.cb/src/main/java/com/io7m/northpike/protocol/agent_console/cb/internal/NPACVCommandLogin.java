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
import com.io7m.northpike.protocol.agent_console.NPACCommandLogin;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1CommandLogin;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVCommandLogin
  implements NPProtocolMessageValidatorType<NPACCommandLogin, NPAC1CommandLogin>
{
  /**
   * A validator.
   */

  COMMAND_LOGIN;

  @Override
  public NPAC1CommandLogin convertToWire(
    final NPACCommandLogin message)
  {
    return new NPAC1CommandLogin(
      new CBUUID(message.messageID()),
      string(message.accessKey())
    );
  }

  @Override
  public NPACCommandLogin convertFromWire(
    final NPAC1CommandLogin message)
  {
    return new NPACCommandLogin(
      message.fieldMessageId().value(),
      message.fieldAccessKey().value()
    );
  }
}
