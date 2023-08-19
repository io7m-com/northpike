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

import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.internal.agents.NPAgentServerSocketService;
import com.io7m.northpike.tls.NPTLSDisabled;
import com.io7m.northpike.tls.NPTLSEnabled;
import com.io7m.northpike.tls.NPTLSStoreConfiguration;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.net.InetAddress;
import java.nio.file.Files;
import java.nio.file.Path;

public final class NPAgentServerSocketServiceTest
{
  @Test
  public void testNoTLS()
    throws Exception
  {
    final var sockets =
      NPAgentServerSocketService.create(
        new NPServerAgentConfiguration(
          InetAddress.getLocalHost(),
          50000,
          NPTLSDisabled.TLS_DISABLED,
          1_000_000
        )
      );

    try (var ignored = sockets.createSocket()) {

    }
  }

  @Test
  public void testWithTLS(
    final @TempDir Path directory)
    throws Exception
  {
    final var file =
      directory.resolve("example.jks");

    try (var stream =
           NPAgentServerSocketServiceTest.class.getResourceAsStream(
      "/com/io7m/northpike/tests/example.jks")) {
      Files.copy(stream, file);
    }

    final var sockets =
      NPAgentServerSocketService.create(
        new NPServerAgentConfiguration(
          InetAddress.getLocalHost(),
          50000,
          new NPTLSEnabled(
            new NPTLSStoreConfiguration(
              "JKS",
              "SUN",
              "12345678",
              file.toAbsolutePath()
            ),
            new NPTLSStoreConfiguration(
              "JKS",
              "SUN",
              "12345678",
              file.toAbsolutePath()
            )
          ),
          1_000_000
        )
      );

    try (var ignored = sockets.createSocket()) {

    }
  }
}
