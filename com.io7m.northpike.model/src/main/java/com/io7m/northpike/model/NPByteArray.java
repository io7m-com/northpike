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

import java.util.Arrays;
import java.util.HexFormat;

/**
 * A byte array with structural equality.
 *
 * @param data The data
 */

public record NPByteArray(
  byte[] data)
{
  /**
   * A byte array with structural equality.
   *
   * @param data The data
   */

  public NPByteArray
  {
    data = data.clone();
  }

  @Override
  public boolean equals(
    final Object o)
  {
    if (this == o) {
      return true;
    }
    if (o == null || !this.getClass().equals(o.getClass())) {
      return false;
    }
    final NPByteArray that = (NPByteArray) o;
    return Arrays.equals(this.data, that.data);
  }

  @Override
  public String toString()
  {
    return HexFormat.of().formatHex(this.data);
  }

  @Override
  public int hashCode()
  {
    return Arrays.hashCode(this.data);
  }
}
