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


package com.io7m.northpike.tests.server.agents;


import com.io7m.northpike.protocol.agent.NPACommandC2SType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.server.internal.agents.NPACmd;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;

import static org.junit.jupiter.api.Assertions.assertNotNull;

public final class NPACmdTest
{
  @SuppressWarnings("unchecked")
  @Provide
  public static Arbitrary<NPACommandC2SType<?>> commands()
  {
    return Arbitraries.defaultFor(NPAMessageType.class)
      .filter(c -> c instanceof NPACommandC2SType<?>)
      .map(NPACommandC2SType.class::cast);
  }

  @Property
  public void testCommandsResolve(
    final @ForAll("commands") NPACommandC2SType<?> command)
  {
    final var cmd =
      NPACmd.create();
    final var exec =
      cmd.resolve(command);

    assertNotNull(exec, "Command %s must resolve".formatted(command.getClass()));
  }
}
