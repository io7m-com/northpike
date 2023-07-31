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

package com.io7m.northpike.protocol.intro.cb;


import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.intro.NPIError;
import com.io7m.northpike.protocol.intro.NPIMessageType;
import com.io7m.northpike.protocol.intro.NPIProtocol;
import com.io7m.northpike.protocol.intro.NPIProtocolsAvailable;

import static com.io7m.northpike.protocol.intro.cb.internal.NPIVError.ERROR;
import static com.io7m.northpike.protocol.intro.cb.internal.NPIVProtocol.PROTOCOL;
import static com.io7m.northpike.protocol.intro.cb.internal.NPIVProtocolsAvailable.PROTOCOLS_AVAILABLE;

/**
 * Functions to translate between the core command set and the Intro
 * Cedarbridge encoding command set.
 */

public final class NPIValidation
  implements NPProtocolMessageValidatorType<NPIMessageType, ProtocolNPIType>
{
  /**
   * Functions to translate between the core command set and the Intro
   * Cedarbridge encoding command set.
   */

  public NPIValidation()
  {

  }

  @Override
  public ProtocolNPIType convertToWire(
    final NPIMessageType message)
    throws NPProtocolException
  {
    if (message instanceof final NPIError m) {
      return ERROR.convertToWire(m);
    }
    if (message instanceof final NPIProtocol m) {
      return PROTOCOL.convertToWire(m);
    }
    if (message instanceof final NPIProtocolsAvailable m) {
      return PROTOCOLS_AVAILABLE.convertToWire(m);
    }
    throw new IllegalStateException();
  }

  @Override
  public NPIMessageType convertFromWire(
    final ProtocolNPIType message)
  {
    if (message instanceof final NPI1Error m) {
      return ERROR.convertFromWire(m);
    }
    if (message instanceof final NPI1Protocol m) {
      return PROTOCOL.convertFromWire(m);
    }
    if (message instanceof final NPI1ProtocolsAvailable m) {
      return PROTOCOLS_AVAILABLE.convertFromWire(m);
    }
    throw new IllegalStateException();
  }
}
