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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.model.NPAgentLabelMatchType.And;
import com.io7m.northpike.model.NPAgentLabelMatchType.Or;
import com.io7m.northpike.model.NPAgentLabelMatchType.Specific;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Combinators;

import static com.io7m.northpike.model.NPAgentLabelMatchType.AnyLabel.ANY_LABEL;

public class NPArbAgentLabelMatch extends NPArbAbstract<NPAgentLabelMatchType>
{
  public NPArbAgentLabelMatch()
  {
    super(
      NPAgentLabelMatchType.class,
      () -> {
        return Arbitraries.oneOf(
          Arbitraries.defaultFor(RDottedName.class)
            .map(Specific::new),

          Arbitraries.create(() -> ANY_LABEL),

          Combinators.combine(
            Arbitraries.defaultFor(RDottedName.class),
            Arbitraries.defaultFor(RDottedName.class),
            Arbitraries.defaultFor(RDottedName.class),
            Arbitraries.defaultFor(RDottedName.class)
          ).as((r0, r1, r2, r3) -> {
            return new Or(
              new And(
                new Specific(r0),
                new Specific(r1)
              ),
              new Or(
                new Specific(r2),
                new Specific(r3)
              )
            );
          }),

          Combinators.combine(
            Arbitraries.defaultFor(RDottedName.class),
            Arbitraries.defaultFor(RDottedName.class),
            Arbitraries.defaultFor(RDottedName.class),
            Arbitraries.defaultFor(RDottedName.class)
          ).as((r0, r1, r2, r3) -> {
            return new And(
              new Or(
                new Specific(r0),
                new Specific(r1)
              ),
              new And(
                new Specific(r2),
                new Specific(r3)
              )
            );
          })
        );
      }
    );
  }
}
