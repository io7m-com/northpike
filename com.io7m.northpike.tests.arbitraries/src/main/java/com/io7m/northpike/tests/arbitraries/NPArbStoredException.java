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


package com.io7m.northpike.tests.arbitraries;

import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPStoredStackTraceElement;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Combinators;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public final class NPArbStoredException
  extends NPArbAbstract<NPStoredException>
{
  public NPArbStoredException()
  {
    super(
      NPStoredException.class,
      () -> {
        return Combinators.combine(
          Arbitraries.strings()
            .ofMaxLength(8),
          Arbitraries.maps(
            Arbitraries.strings().ofMaxLength(8),
            Arbitraries.strings().ofMaxLength(8)
          ),
          Arbitraries.defaultFor(NPStoredStackTraceElement.class)
            .list()
        ).as((msg, attrs, stack) -> {
          return new NPStoredException(
            IOException.class.getCanonicalName(),
            msg,
            attrs,
            Optional.of(leaf()),
            leaves(),
            stack
          );
        });
      }
    );
  }

  private static NPStoredException leaf()
  {
    return NPStoredException.ofException(new IOException("Leaf!"));
  }

  private static List<NPStoredException> leaves()
  {
    final var results =
      new ArrayList<NPStoredException>();
    final var bound =
      Arbitraries.integers()
        .between(0, 5)
        .sample();

    for (int index = 0; index < bound.intValue(); ++index) {
      results.add(
        NPStoredException.ofException(
          new IOException("Leaf %d".formatted(Integer.valueOf(index)))
        )
      );
    }
    return results;
  }
}
