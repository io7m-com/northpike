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

import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import com.io7m.northpike.toolexec.model.NPTXEAnd;
import com.io7m.northpike.toolexec.model.NPTXEFalse;
import com.io7m.northpike.toolexec.model.NPTXEInteger;
import com.io7m.northpike.toolexec.model.NPTXEIsEqual;
import com.io7m.northpike.toolexec.model.NPTXENot;
import com.io7m.northpike.toolexec.model.NPTXEOr;
import com.io7m.northpike.toolexec.model.NPTXEString;
import com.io7m.northpike.toolexec.model.NPTXEStringSetContains;
import com.io7m.northpike.toolexec.model.NPTXETrue;
import com.io7m.northpike.toolexec.model.NPTXEVariableBoolean;
import com.io7m.northpike.toolexec.model.NPTXEVariableInteger;
import com.io7m.northpike.toolexec.model.NPTXEVariableString;
import com.io7m.northpike.toolexec.model.NPTXEVariableStringSet;
import com.io7m.northpike.toolexec.model.NPTXExpressionType;
import net.jqwik.api.Arbitraries;

import java.util.List;

public final class NPArbExpressionType extends NPArbAbstract<NPTXExpressionType>
{
  public NPArbExpressionType()
  {
    super(
      NPTXExpressionType.class,
      () -> {
        return Arbitraries.oneOf(
          List.of(
            Arbitraries.defaultFor(NPTXEAnd.class),
            Arbitraries.defaultFor(NPTXEFalse.class),
            Arbitraries.defaultFor(NPTXEIsEqual.class),
            Arbitraries.defaultFor(NPTXENot.class),
            Arbitraries.defaultFor(NPTXEInteger.class),
            Arbitraries.defaultFor(NPTXEOr.class),
            Arbitraries.defaultFor(NPTXEString.class),
            Arbitraries.defaultFor(NPTXEStringSetContains.class),
            Arbitraries.defaultFor(NPTXETrue.class),
            Arbitraries.defaultFor(NPTXEVariableBoolean.class),
            Arbitraries.defaultFor(NPTXEVariableInteger.class),
            Arbitraries.defaultFor(NPTXEVariableString.class),
            Arbitraries.defaultFor(NPTXEVariableStringSet.class)
          )
        );
      }
    );
  }
}
