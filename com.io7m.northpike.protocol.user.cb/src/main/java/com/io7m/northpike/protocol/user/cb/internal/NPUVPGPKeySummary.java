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
import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPPublicKeySummary;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1PGPKeySummary;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVPGPKeySummary
  implements NPProtocolMessageValidatorType<NPPublicKeySummary, NPU1PGPKeySummary>
{
  /**
   * A validator.
   */

  PGP_KEY_SUMMARY;

  @Override
  public NPU1PGPKeySummary convertToWire(
    final NPPublicKeySummary message)
  {
    return new NPU1PGPKeySummary(
      string(message.userID()),
      string(message.fingerprint().value()),
      new CBOffsetDateTime(message.timeCreated()),
      CBOptionType.fromOptional(message.timeExpires().map(CBOffsetDateTime::new))
    );
  }

  @Override
  public NPPublicKeySummary convertFromWire(
    final NPU1PGPKeySummary message)
  {
    return new NPPublicKeySummary(
      message.fieldUserId().value(),
      new NPFingerprint(message.fieldFingerprint().value()),
      message.fieldTimeCreated().value(),
      message.fieldTimeExpires().asOptional()
        .map(CBOffsetDateTime::value)
    );
  }
}
