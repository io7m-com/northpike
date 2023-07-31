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

import com.io7m.northpike.protocol.agent.NPACommandLogin;
import com.io7m.northpike.protocol.agent.cb.NPA1CommandLogin;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVKey.KEY;

/**
 * A validator.
 */

public enum NPAVCommandLogin
  implements NPProtocolMessageValidatorType<NPACommandLogin, NPA1CommandLogin>
{
  /**
   * A validator.
   */

  COMMAND_LOGIN;

  @Override
  public NPA1CommandLogin convertToWire(
    final NPACommandLogin message)
  {
    return new NPA1CommandLogin(KEY.convertToWire(message.key()));
  }

  @Override
  public NPACommandLogin convertFromWire(
    final NPA1CommandLogin message)
  {
    return new NPACommandLogin(KEY.convertFromWire(message.fieldKey()));
  }
}
