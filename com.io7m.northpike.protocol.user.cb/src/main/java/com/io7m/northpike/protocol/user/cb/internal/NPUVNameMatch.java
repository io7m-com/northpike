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

import com.io7m.northpike.model.NPNameMatchType;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1NameMatch;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVNameMatch
  implements NPProtocolMessageValidatorType<NPNameMatchType, NPU1NameMatch>
{
  /**
   * A validator.
   */

  NAME_MATCH;

  @Override
  public NPU1NameMatch convertToWire(
    final NPNameMatchType message)
  {
    if (message instanceof NPNameMatchType.AnyName) {
      return new NPU1NameMatch.AnyName();
    }

    if (message instanceof final NPNameMatchType.Similar similar) {
      return new NPU1NameMatch.Similar(string(similar.name()));
    }

    if (message instanceof final NPNameMatchType.Exact exact) {
      return new NPU1NameMatch.Exact(string(exact.name()));
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPNameMatchType convertFromWire(
    final NPU1NameMatch message)
  {
    if (message instanceof NPU1NameMatch.AnyName) {
      return NPNameMatchType.AnyName.ANY_NAME;
    }

    if (message instanceof final NPU1NameMatch.Exact exact) {
      return new NPNameMatchType.Exact(exact.fieldName().value());
    }

    if (message instanceof final NPU1NameMatch.Similar similar) {
      return new NPNameMatchType.Similar(similar.fieldName().value());
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
