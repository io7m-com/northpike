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


package com.io7m.northpike.tests.server;

import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.api.NPDatabaseCreate;
import com.io7m.northpike.database.api.NPDatabaseFactoryType;
import com.io7m.northpike.database.api.NPDatabaseUpgrade;
import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerArchiveConfiguration;
import com.io7m.northpike.server.api.NPServerConfiguration;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.strings.NPStrings;

import java.net.InetAddress;
import java.net.URI;
import java.nio.file.Paths;
import java.time.Clock;
import java.util.Locale;
import java.util.Optional;

import static com.io7m.northpike.tls.NPTLSDisabled.TLS_DISABLED;

/**
 * Fake server configurations for tests.
 */

public final class NPServerConfigurations
{
  private NPServerConfigurations()
  {

  }

  public static NPServerConfiguration createFakeServerConfiguration(
    final NPStrings strings,
    final NPDatabaseFactoryType databases)
    throws Exception
  {
    return new NPServerConfiguration(
      Locale.ROOT,
      Clock.systemUTC(),
      strings,
      databases,
      new NPDatabaseConfiguration(
        "northpike_install",
        "12345678",
        "12345678",
        Optional.of("12345678"),
        "localhost",
        15432,
        "northpike",
        NPDatabaseCreate.CREATE_DATABASE,
        NPDatabaseUpgrade.UPGRADE_DATABASE,
        false,
        "english",
        Clock.systemUTC(),
        strings
      ),
      new NPServerDirectoryConfiguration(
        Paths.get("repositories"),
        Paths.get("archives")),
      new NPServerIdstoreConfiguration(
        URI.create("http://localhost:30000"),
        URI.create("http://localhost:30000")
      ),
      new NPServerAgentConfiguration(
        InetAddress.getLocalHost(),
        20048,
        TLS_DISABLED,
        1000000
      ),
      new NPServerArchiveConfiguration(
        InetAddress.getLocalHost(),
        40001,
        TLS_DISABLED
      ),
      Optional.empty()
    );
  }
}
