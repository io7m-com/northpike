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
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.cb.NPU1CommandLogin;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVIdName.ID_NAME;

/**
 * A validator.
 */

public enum NPUVCommandLogin
  implements NPProtocolMessageValidatorType<NPUCommandLogin, NPU1CommandLogin>
{
  /**
   * A validator.
   */

  COMMAND_LOGIN;

  @Override
  public NPU1CommandLogin convertToWire(
    final NPUCommandLogin message)
  {
    return new NPU1CommandLogin(
      new CBUUID(message.messageID()),
      ID_NAME.convertToWire(message.name()),
      string(message.password())
    );
  }

  @Override
  public NPUCommandLogin convertFromWire(
    final NPU1CommandLogin message)
  {
    return new NPUCommandLogin(
      message.fieldMessageId().value(),
      ID_NAME.convertFromWire(message.fieldUserName()),
      message.fieldPassword().value()
    );
  }
}
