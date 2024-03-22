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

import com.io7m.cedarbridge.runtime.api.CBBooleanType;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1VersionRange;
import com.io7m.verona.core.VersionRange;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVVersion.VERSION;

/**
 * A validator.
 */

public enum NPUVVersionRange
  implements NPProtocolMessageValidatorType<VersionRange, NPU1VersionRange>
{
  /**
   * A validator.
   */

  VERSION_RANGE;

  @Override
  public NPU1VersionRange convertToWire(
    final VersionRange message)
  {
    return new NPU1VersionRange(
      VERSION.convertToWire(message.lower()),
      CBBooleanType.fromBoolean(message.lowerInclusive()),
      VERSION.convertToWire(message.upper()),
      CBBooleanType.fromBoolean(message.upperInclusive())
    );
  }

  @Override
  public VersionRange convertFromWire(
    final NPU1VersionRange message)
  {
    return new VersionRange(
      VERSION.convertFromWire(message.fieldLower()),
      message.fieldLowerInclusive().asBoolean(),
      VERSION.convertFromWire(message.fieldUpper()),
      message.fieldUpperInclusive().asBoolean()
    );
  }
}
