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


package com.io7m.northpike.tests.agent.workexec;

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.bssio.CBSerializationContextBSSIO;
import com.io7m.jbssio.vanilla.BSSWriters;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.cb.NPA1Messages;
import net.jqwik.api.Arbitraries;

import java.nio.file.Files;
import java.nio.file.Paths;

public final class NPWorkExecDemo
{
  private NPWorkExecDemo()
  {

  }

  public static void main(
    final String[] args)
    throws Exception
  {
    final var cmd =
      Arbitraries.defaultFor(NPACommandSWorkSent.class)
        .sample();

    try (var output = Files.newOutputStream(Paths.get("/tmp/data.bin"))) {
      final var context =
        CBSerializationContextBSSIO.createFromOutputStream(
          new BSSWriters(),
          output
        );

      final var messages = new NPA1Messages();
      CBUUID.serialize(context, new CBUUID(NPA1Messages.protocolId()));
      context.writeU32(1L);
      messages.writeLengthPrefixed(output, cmd);
      output.flush();
    }
  }
}
