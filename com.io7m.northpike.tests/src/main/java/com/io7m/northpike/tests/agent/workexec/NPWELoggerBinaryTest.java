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

import com.io7m.cedarbridge.runtime.bssio.CBSerializationContextBSSIO;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.jbssio.vanilla.BSSReaders;
import com.io7m.northpike.agent.workexec.api.NPAWorkEvent;
import com.io7m.northpike.agent.workexec.local.cb.NWEOutput;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWE;
import com.io7m.northpike.agent.workexec.main.internal.NPWELoggerBinary;
import com.io7m.northpike.model.NPStoredException;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.net.URI;
import java.nio.ByteBuffer;
import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.agent.workexec.api.NPAWorkEvent.Severity.ERROR;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

public final class NPWELoggerBinaryTest
{
  private static final BSSReaderProviderType READERS =
    new BSSReaders();

  @Test
  public void testLog()
    throws Exception
  {
    final var out =
      new ByteArrayOutputStream();
    final var logger =
      NPWELoggerBinary.create(out);

    final var time =
      OffsetDateTime.now();
    final var ex =
      new IOException("I/O error.");

    logger.initialize();

    final var event =
      new NPAWorkEvent(
        ERROR,
        time,
        "A",
        Map.ofEntries(
          Map.entry("a", "x"),
          Map.entry("b", "y"),
          Map.entry("c", "z")
        ),
        Optional.of(NPStoredException.ofException(ex))
      );

    logger.logWorkEvent(event);
    logger.logWorkEvent(event);
    logger.logWorkEvent(event);

    final var reader =
      READERS.createReaderFromByteBuffer(
        URI.create("stdin"),
        ByteBuffer.wrap(out.toByteArray()),
        "root"
      );

    final var magic = reader.readU32BE();
    assertEquals(0x4e505745L, magic);
    final var version = reader.readU32BE();
    assertEquals(1L, version);

    final var serializer =
      new ProtocolNWE()
        .serializerForProtocolVersion(1L)
        .orElseThrow();

    int count = 0;

    while (true) {
      if (reader.bytesRemaining().orElse(0L) == 0L) {
        break;
      }

      final var length = reader.readU32BE();
      final var buffer = new byte[(int) length];
      reader.readBytes(buffer);

      final var ctx =
        CBSerializationContextBSSIO.createFromByteArray(READERS, buffer);
      final var output =
        assertInstanceOf(NWEOutput.class, serializer.deserialize(ctx));

      assertEquals(
        event.message(),
        output.fieldOutput().value()
      );
      assertEquals(
        event.attributes(),
        CBMaps.toMapString(output.fieldAttributes())
      );
      assertEquals(
        event.time(),
        output.fieldTimestamp().value()
      );
      assertEquals(
        event.exception().orElseThrow(),
        NPStoredException.ofException(ex)
      );

      ++count;
    }

    assertEquals(3, count);
  }
}
