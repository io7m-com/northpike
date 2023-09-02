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
import com.io7m.northpike.toolexec.model.NPTXPlanVariableType;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;

import java.util.HashMap;

public final class NPArbPlanVariables
  extends NPArbAbstract<NPTXPlanVariables>
{
  public NPArbPlanVariables()
  {
    super(
      NPTXPlanVariables.class,
      NPArbPlanVariables::generate
    );
  }

  private static Arbitrary<NPTXPlanVariables> generate()
  {
    return Arbitraries.create(() -> {
      final var m =
        new HashMap<RDottedName, NPTXPlanVariableType>();
      final var vars =
        Arbitraries.defaultFor(NPTXPlanVariableType.class)
          .list()
          .ofMinSize(0)
          .ofMaxSize(8)
          .sample();

      for (final var v : vars) {
        m.put(v.name(), v);
      }
      return new NPTXPlanVariables(m);
    });
  }
}
