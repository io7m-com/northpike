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
import com.io7m.jbssio.api.BSSReaderProviderType;
import com.io7m.jbssio.api.BSSReaderSequentialType;
import com.io7m.jbssio.vanilla.BSSReaders;
import com.io7m.northpike.agent.workexec.local.cb.ProtocolNWE;
import org.apache.commons.io.input.ProxyInputStream;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Paths;

public final class NPWorkExecBinaryLoggerDemo
{
  private NPWorkExecBinaryLoggerDemo()
  {

  }

  private static final class CloseShieldInputStream
    extends ProxyInputStream
  {
    CloseShieldInputStream(
      final InputStream proxy)
    {
      super(proxy);
    }

    @Override
    public void close()
    {

    }
  }

  private static final BSSReaderProviderType READERS =
    new BSSReaders();
  private static final ProtocolNWE PROTOCOL =
    new ProtocolNWE();

  public static void main(
    final String[] args)
    throws Exception
  {
    final var input =
      new CloseShieldInputStream(
        Files.newInputStream(Paths.get("/tmp/podman.bin")));

    final var reader =
      READERS.createReaderFromStream(URI.create("stdin"), input, "root");

    reader.readU32BE();
    reader.readU32BE();

    final var inputDeserializer =
      PROTOCOL.serializerForProtocolVersion(1L)
        .orElseThrow();

    while (true) {
      System.out.printf("Offset: %d%n", reader.offsetCurrentAbsolute());

      final var lengthReader =
        reader.createSubReaderBounded("length", 4L);
      final var length =
        lengthReader.readU32BE();

      final var dataReader =
        reader.createSubReaderBounded("data", length);

      System.out.printf(
        "Length: %d (0x%x)%n",
        Long.valueOf(length),
        Long.valueOf(length)
      );

      final var buffer = new byte[(int) length];
      dataReader.readBytes(buffer);

      dumpHex(buffer);

      final var inputContext =
        CBSerializationContextBSSIO.createFromByteArray(READERS, buffer);

      inputDeserializer.deserialize(inputContext);
    }
  }

  private static void dumpHex(
    final byte[] buffer)
  {
    System.out.println();
    for (int index = 0; index < buffer.length; ++index) {
      System.out.printf("%02x ", buffer[index]);
      if (index == 0) {
        continue;
      }
      if ((index + 1) % 16 == 0) {
        System.out.println();
      }
    }
    System.out.println();
    System.out.println();
  }

  private static BSSReaderSequentialType createBoundedReader(
    final InputStream stream,
    final long size)
    throws IOException
  {
    return READERS.createReaderFromStreamBounded(
      URI.create("stdin"),
      stream,
      "root",
      size
    );
  }
}
