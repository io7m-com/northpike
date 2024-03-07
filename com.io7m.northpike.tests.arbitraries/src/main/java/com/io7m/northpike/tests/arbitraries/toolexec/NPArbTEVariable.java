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


package com.io7m.northpike.tests.arbitraries.toolexec;

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import com.io7m.northpike.toolexec.program.api.NPTPVariableBoolean;
import com.io7m.northpike.toolexec.program.api.NPTPVariableInteger;
import com.io7m.northpike.toolexec.program.api.NPTPVariableString;
import com.io7m.northpike.toolexec.program.api.NPTPVariableStringSet;
import com.io7m.northpike.toolexec.program.api.NPTPVariableType;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.Combinators;

public final class NPArbTEVariable extends NPArbAbstract<NPTPVariableType>
{
  public NPArbTEVariable()
  {
    super(
      NPTPVariableType.class,
      () -> Arbitraries.oneOf(
        booleans(),
        integers(),
        strings(),
        stringSets()
      )
    );
  }

  private static Arbitrary<NPTPVariableType> stringSets()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(RDottedName.class),
      Arbitraries.strings().set()
    ).as(NPTPVariableStringSet::new);
  }

  private static Arbitrary<NPTPVariableType> strings()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(RDottedName.class),
      Arbitraries.strings()
    ).as(NPTPVariableString::new);
  }

  private static Arbitrary<NPTPVariableType> integers()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(RDottedName.class),
      Arbitraries.bigIntegers()
    ).as(NPTPVariableInteger::new);
  }

  private static Arbitrary<NPTPVariableType> booleans()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(RDottedName.class),
      Arbitraries.integers()
        .map(x -> x % 2 == 0)
    ).as(NPTPVariableBoolean::new);
  }
}
