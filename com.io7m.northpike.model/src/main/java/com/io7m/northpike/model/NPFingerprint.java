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

package com.io7m.northpike.model;

import java.util.Objects;
import java.util.regex.Pattern;

/**
 * A fingerprint of a public key.
 *
 * @param value The fingerprint value
 *
 * @see "https://www.rfc-editor.org/rfc/rfc4880#section-12.2"
 */

public record NPFingerprint(String value)
{
  private static final Pattern VALID_FINGERPRINT =
    Pattern.compile("[0-9a-f]{40}");

  /**
   * A fingerprint of a public key.
   *
   * @param value The fingerprint value
   *
   * @see "https://www.rfc-editor.org/rfc/rfc4880#section-12.2"
   */

  public NPFingerprint
  {
    Objects.requireNonNull(value, "value");

    if (!VALID_FINGERPRINT.matcher(value).matches()) {
      throw new NPValidityException(
        "Fingerprints must match %s".formatted(VALID_FINGERPRINT)
      );
    }
  }

  /**
   * @return That pattern that defines a valid fingerprint
   */

  public static String syntax()
  {
    return VALID_FINGERPRINT.pattern();
  }

  @Override
  public String toString()
  {
    return this.value;
  }
}
