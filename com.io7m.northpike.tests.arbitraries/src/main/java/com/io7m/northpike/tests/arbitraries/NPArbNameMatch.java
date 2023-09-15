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

import com.io7m.northpike.model.NPNameMatchType;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;

import static com.io7m.northpike.model.NPNameMatchType.AnyName.ANY_NAME;

public final class NPArbNameMatch extends NPArbAbstract<NPNameMatchType>
{
  public NPArbNameMatch()
  {
    super(
      NPNameMatchType.class,
      () -> {
        return Arbitraries.oneOf(
          any(),
          exact(),
          similar()
        );
      }
    );
  }

  private static Arbitrary<NPNameMatchType> any()
  {
    return Arbitraries.create(() -> ANY_NAME);
  }

  private static Arbitrary<NPNameMatchType> exact()
  {
    return Arbitraries.strings().alpha().map(NPNameMatchType.Exact::new);
  }

  private static Arbitrary<NPNameMatchType> similar()
  {
    return Arbitraries.strings().alpha().map(NPNameMatchType.Similar::new);
  }
}
