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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1Version;
import com.io7m.verona.core.Version;
import com.io7m.verona.core.VersionQualifier;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;

/**
 * A validator.
 */

public enum NPUVVersion
  implements NPProtocolMessageValidatorType<Version, NPU1Version>
{
  /**
   * A validator.
   */

  VERSION;

  @Override
  public NPU1Version convertToWire(
    final Version message)
  {
    return new NPU1Version(
      unsigned32(message.major()),
      unsigned32(message.minor()),
      unsigned32(message.patch()),
      CBOptionType.fromOptional(
        message.qualifier()
          .map(x -> string(x.text()))
      )
    );
  }

  @Override
  public Version convertFromWire(
    final NPU1Version message)
  {
    return new Version(
      Math.toIntExact(message.fieldMajor().value()),
      Math.toIntExact(message.fieldMinor().value()),
      Math.toIntExact(message.fieldPatch().value()),
      message.fieldQualifier()
        .asOptional()
        .map(x -> new VersionQualifier(x.value()))
    );
  }
}
