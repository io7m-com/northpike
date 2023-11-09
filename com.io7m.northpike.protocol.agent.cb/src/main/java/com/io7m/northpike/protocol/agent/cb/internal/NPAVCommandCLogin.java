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
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.cb.NPA1CommandCLogin;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVAgentPublicKey.PUBLIC_KEY;

/**
 * A validator.
 */

public enum NPAVCommandCLogin
  implements NPProtocolMessageValidatorType<NPACommandCLogin, NPA1CommandCLogin>
{
  /**
   * A validator.
   */

  COMMAND_LOGIN;

  @Override
  public NPA1CommandCLogin convertToWire(
    final NPACommandCLogin message)
  {
    return new NPA1CommandCLogin(
      new CBUUID(message.messageID()),
      PUBLIC_KEY.convertToWire(message.key())
    );
  }

  @Override
  public NPACommandCLogin convertFromWire(
    final NPA1CommandCLogin message)
    throws NPProtocolException
  {
    return new NPACommandCLogin(
      message.fieldMessageId().value(),
      PUBLIC_KEY.convertFromWire(message.fieldKey())
    );
  }
}
