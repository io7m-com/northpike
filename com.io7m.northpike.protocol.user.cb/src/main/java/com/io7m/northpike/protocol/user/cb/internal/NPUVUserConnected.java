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
import com.io7m.idstore.model.IdName;
import com.io7m.northpike.model.NPUserConnected;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1UserConnected;

import java.net.InetSocketAddress;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned16;

/**
 * A validator.
 */

public enum NPUVUserConnected
  implements NPProtocolMessageValidatorType<NPUserConnected, NPU1UserConnected>
{
  /**
   * A validator.
   */

  USER_CONNECTED;

  @Override
  public NPU1UserConnected convertToWire(
    final NPUserConnected message)
  {
    return new NPU1UserConnected(
      new CBUUID(message.userId()),
      string(message.name().value()),
      string(message.address().toString()),
      unsigned16(message.address().getPort())
    );
  }

  @Override
  public NPUserConnected convertFromWire(
    final NPU1UserConnected message)
  {
    final var split =
      message.fieldAddress()
        .value()
        .split("/");

    return new NPUserConnected(
      message.fieldId().value(),
      new IdName(message.fieldName().value()),
      InetSocketAddress.createUnresolved(
        split[0],
        message.fieldPort().value()
      )
    );
  }
}
