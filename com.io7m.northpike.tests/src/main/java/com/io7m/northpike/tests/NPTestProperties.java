/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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

package com.io7m.northpike.tests;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Properties;

public final class NPTestProperties
{
  public static final Path WORKEXEC_DISTRIBUTION;
  public static final String POSTGRESQL_VERSION;
  public static final String IDSTORE_VERSION;
  public static final String QUIXOTE_VERSION;

  static  {
    final var properties = new Properties();

    try {
      try (var stream = NPTestProperties.class.getResourceAsStream(
        "/northpike-test.properties")) {
        properties.load(stream);
      }
    } catch (final IOException e) {
      throw new IllegalStateException(e);
    }

    WORKEXEC_DISTRIBUTION =
      Paths.get(properties.getProperty("workexec.distribution"));
    POSTGRESQL_VERSION =
      properties.getProperty("containers.postgresql.version");
    IDSTORE_VERSION =
      properties.getProperty("containers.idstore.version");
    QUIXOTE_VERSION =
      properties.getProperty("com.io7m.quixote.version");
  }

  private NPTestProperties()
  {

  }
}
