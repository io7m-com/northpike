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


package com.io7m.northpike.shell.internal;

import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryCredentialsType;
import com.io7m.northpike.model.NPRepositoryCredentialsUsernamePassword;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.Objects;

/**
 * @see NPRepositoryCredentialsType
 */

public final class NPRepositoryCredentialsConverter
  implements QValueConverterType<NPRepositoryCredentialsType>
{
  /**
   * @see NPRepositoryCredentialsType
   */

  public NPRepositoryCredentialsConverter()
  {

  }

  @Override
  public NPRepositoryCredentialsType convertFromString(
    final String text)
  {
    if (Objects.equals(text, "none")) {
      return NPRepositoryCredentialsNone.CREDENTIALS_NONE;
    }

    if (text.startsWith("username-password:")) {
      final var segments = text.split(":");
      if (segments.length == 3) {
        return new NPRepositoryCredentialsUsernamePassword(
          segments[1],
          segments[2]
        );
      }
    }

    throw new IllegalArgumentException("Unparseable credentials.");
  }

  @Override
  public String convertToString(
    final NPRepositoryCredentialsType value)
  {
    if (value instanceof NPRepositoryCredentialsNone) {
      return "none";
    }
    if (value instanceof final NPRepositoryCredentialsUsernamePassword up) {
      return "username-password:%s:%s".formatted(up.userName(), up.password());
    }
    throw new IllegalStateException("Unrecognized credentials type: " + value);
  }

  @Override
  public NPRepositoryCredentialsType exampleValue()
  {
    return new NPRepositoryCredentialsUsernamePassword(
      "oscar",
      "YdqFvBV/3uN7ywoGWgAU"
    );
  }

  @Override
  public String syntax()
  {
    return "none | username-password:<user>:<password>";
  }

  @Override
  public Class<NPRepositoryCredentialsType> convertedClass()
  {
    return NPRepositoryCredentialsType.class;
  }
}
