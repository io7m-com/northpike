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

import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

/**
 * Functions to validate maps.
 */

public final class NPMapValidation
{
  private NPMapValidation()
  {

  }

  /**
   * Check map invariants such as keys comparisons the extracted value keys.
   *
   * @param m   The map
   * @param key The key extraction function
   * @param <A> The type of keys
   * @param <B> The type of values
   */

  public static <A, B> void check(
    final Map<A, B> m,
    final Function<B, A> key)
  {
    Objects.requireNonNull(m, "m");
    Objects.requireNonNull(key, "key");

    for (final var e : m.entrySet()) {
      final var xk = key.apply(e.getValue());
      if (!Objects.equals(e.getKey(), xk)) {
        throw new NPValidityException(
          "Key %s does not match extracted key %s of %s"
            .formatted(e.getKey(), xk, e.getValue())
        );
      }
    }
  }
}
