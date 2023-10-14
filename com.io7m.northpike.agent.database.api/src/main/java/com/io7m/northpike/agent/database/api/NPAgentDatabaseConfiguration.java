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

package com.io7m.northpike.agent.database.api;


import com.io7m.northpike.strings.NPStrings;

import java.nio.file.Path;
import java.time.Clock;
import java.util.Objects;

/**
 * The agent database configuration.
 *
 * @param upgrade           The upgrade specification
 * @param create            The creation specification
 * @param databaseFile      The database file
 * @param clock             A clock for time retrievals
 * @param strings           The string resources
 * @param language          The language used for databases (such as 'english')
 */

public record NPAgentDatabaseConfiguration(
  Path databaseFile,
  NPAgentDatabaseCreate create,
  NPAgentDatabaseUpgrade upgrade,
  String language,
  Clock clock,
  NPStrings strings)
{
  /**
   * The agent database configuration.
   *
   * @param upgrade           The upgrade specification
   * @param create            The creation specification
   * @param databaseFile      The database file
   * @param clock             A clock for time retrievals
   * @param strings           The string resources
   * @param language          The language used for databases (such as 'english')
   */

  public NPAgentDatabaseConfiguration
  {
    Objects.requireNonNull(databaseFile, "databaseFile");
    Objects.requireNonNull(create, "create");
    Objects.requireNonNull(upgrade, "upgrade");
    Objects.requireNonNull(clock, "clock");
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(language, "language");
  }
}
