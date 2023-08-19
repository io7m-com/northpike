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


package com.io7m.northpike.server.configuration;

import com.io7m.northpike.server.api.NPServerAgentConfiguration;
import com.io7m.northpike.server.api.NPServerArchiveConfiguration;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerIdstoreConfiguration;
import com.io7m.northpike.telemetry.api.NPTelemetryConfiguration;

import java.util.Objects;
import java.util.Optional;

/**
 * A configuration file.
 *
 * @param databaseConfiguration  The database configuration
 * @param directoryConfiguration The directory configuration
 * @param idstoreConfiguration   The idstore configuration
 * @param agentConfiguration     The agent configuration
 * @param archiveConfiguration   The archive configuration
 * @param openTelemetry          The telemetry configuration
 */

public record NPSCFile(
  NPSCDatabase databaseConfiguration,
  NPServerDirectoryConfiguration directoryConfiguration,
  NPServerIdstoreConfiguration idstoreConfiguration,
  NPServerAgentConfiguration agentConfiguration,
  NPServerArchiveConfiguration archiveConfiguration,
  Optional<NPTelemetryConfiguration> openTelemetry)
{
  /**
   * A configuration file.
   *
   * @param databaseConfiguration  The database configuration
   * @param directoryConfiguration The directory configuration
   * @param idstoreConfiguration   The idstore configuration
   * @param agentConfiguration     The agent configuration
   * @param archiveConfiguration   The archive configuration
   * @param openTelemetry          The telemetry configuration
   */

  public NPSCFile
  {
    Objects.requireNonNull(agentConfiguration, "agentConfiguration");
    Objects.requireNonNull(archiveConfiguration, "archiveConfiguration");
    Objects.requireNonNull(databaseConfiguration, "databaseConfiguration");
    Objects.requireNonNull(directoryConfiguration, "directoryConfiguration");
    Objects.requireNonNull(idstoreConfiguration, "idstoreConfiguration");
    Objects.requireNonNull(openTelemetry, "openTelemetry");
  }
}
