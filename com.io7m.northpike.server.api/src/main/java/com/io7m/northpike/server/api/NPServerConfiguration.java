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

package com.io7m.northpike.server.api;

import com.io7m.northpike.database.api.NPDatabaseConfiguration;
import com.io7m.northpike.database.api.NPDatabaseFactoryType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration;

import java.time.Clock;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;

/**
 * The configuration for a server.
 *
 * @param clock                 The clock
 * @param strings               The string resources
 * @param databaseConfiguration The database configuration for the server
 * @param databases             The factory of databases that will be used for
 *                              the server
 * @param directories           The server directories
 * @param locale                The locale
 * @param idstoreConfiguration  The idstore configuration
 * @param agentConfiguration    The agent service configuration
 * @param openTelemetry         The OpenTelemetry configuration
 */

public record NPServerConfiguration(
  Locale locale,
  Clock clock,
  NPStrings strings,
  NPDatabaseFactoryType databases,
  NPDatabaseConfiguration databaseConfiguration,
  NPServerDirectoryConfiguration directories,
  NPServerIdstoreConfiguration idstoreConfiguration,
  NPServerAgentConfiguration agentConfiguration,
  Optional<NPTelemetryConfiguration> openTelemetry)
{
  /**
   * The configuration for a server.
   *
   * @param clock                 The clock
   * @param strings               The string resources
   * @param databaseConfiguration The database configuration for the server
   * @param databases             The factory of databases that will be used for
   *                              the server
   * @param directories           The server directories
   * @param locale                The locale
   * @param idstoreConfiguration  The idstore configuration
   * @param agentConfiguration    The agent service configuration
   * @param openTelemetry         The OpenTelemetry configuration
   */

  public NPServerConfiguration
  {
    Objects.requireNonNull(agentConfiguration, "agentConfiguration");
    Objects.requireNonNull(clock, "clock");
    Objects.requireNonNull(databaseConfiguration, "databaseConfiguration");
    Objects.requireNonNull(databases, "databases");
    Objects.requireNonNull(directories, "directories");
    Objects.requireNonNull(idstoreConfiguration, "idstoreConfiguration");
    Objects.requireNonNull(locale, "locale");
    Objects.requireNonNull(openTelemetry, "openTelemetry");
    Objects.requireNonNull(strings, "strings");
  }
}
