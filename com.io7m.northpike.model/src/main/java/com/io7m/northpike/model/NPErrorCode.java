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
 * The type of error codes.
 *
 * @param id The error code identifier
 */

public record NPErrorCode(String id)
{
  private static final Pattern VALID_ERROR_CODE =
    Pattern.compile("[a-z][a-z\\-]+");

  /**
   * The type of error codes.
   *
   * @param id The error code identifier
   */

  public NPErrorCode
  {
    Objects.requireNonNull(id, "id");

    if (!VALID_ERROR_CODE.matcher(id).matches()) {
      throw new NPValidityException(
        "Error code identifiers must match %s".formatted(VALID_ERROR_CODE)
      );
    }
  }

  @Override
  public String toString()
  {
    return this.id;
  }
}
