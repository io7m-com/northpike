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

import com.io7m.northpike.model.NPAgentResourceName;
import com.io7m.northpike.model.NPAgentWorkItem;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.model.NPToolReference;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Combinators;

public final class NPArbAgentWorkItem extends NPArbAbstract<NPAgentWorkItem>
{
  public NPArbAgentWorkItem()
  {
    super(
      NPAgentWorkItem.class,
      () ->
        Combinators.combine(
          Arbitraries.defaultFor(NPWorkItemIdentifier.class),
          Arbitraries.maps(
            Arbitraries.strings().alpha(),
            Arbitraries.strings().alpha()
          ).ofMaxSize(8),
          Arbitraries.defaultFor(NPToolReference.class)
            .set()
            .ofMaxSize(8),
          Arbitraries.defaultFor(NPToolExecutionEvaluated.class),
          Arbitraries.defaultFor(NPAgentResourceName.class)
            .set()
            .ofMaxSize(8)
        ).as(NPAgentWorkItem::new)
    );
  }
}
