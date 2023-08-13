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

package com.io7m.northpike.database.api;


import com.io7m.northpike.strings.NPStrings;

import java.time.Clock;
import java.util.Objects;
import java.util.Optional;

/**
 * The server database configuration.
 *
 * @param ownerRoleName      The name of the role that owns the database; used for database setup and migrations
 * @param ownerRolePassword  The password of the role that owns the database
 * @param workerRolePassword The password of the worker role used for normal database operation
 * @param readerRolePassword The password of the role used for read-only database access
 * @param port               The database TCP/IP port
 * @param upgrade            The upgrade specification
 * @param create             The creation specification
 * @param address            The database address
 * @param databaseName       The database name
 * @param clock              A clock for time retrievals
 * @param strings            The string resources
 * @param language           The language used for databases (such as 'english')
 * @param useTLS             {@code true} if TLS should be used for database connections
 */

public record NPDatabaseConfiguration(
  String ownerRoleName,
  String ownerRolePassword,
  String workerRolePassword,
  Optional<String> readerRolePassword,
  String address,
  int port,
  String databaseName,
  NPDatabaseCreate create,
  NPDatabaseUpgrade upgrade,
  boolean useTLS,
  String language,
  Clock clock,
  NPStrings strings)
{
  /**
   * The server database configuration.
   *
   * @param ownerRoleName      The name of the role that owns the database;
   *                           used for database setup and migrations
   * @param ownerRolePassword  The password of the role that owns the database
   * @param workerRolePassword The password of the worker role used for normal
   *                           database operation
   * @param readerRolePassword The password of the role used for read-only
   *                           database access
   * @param port               The database TCP/IP port
   * @param upgrade            The upgrade specification
   * @param create             The creation specification
   * @param address            The database address
   * @param databaseName       The database name
   * @param clock              A clock for time retrievals
   * @param strings            The string resources
   * @param language           The language used for databases
   *                           (such as 'english')
   * @param useTLS             {@code true} if TLS should be used for database connections
   */

  public NPDatabaseConfiguration
  {
    Objects.requireNonNull(ownerRoleName, "ownerRoleName");
    Objects.requireNonNull(ownerRolePassword, "ownerRolePassword");
    Objects.requireNonNull(workerRolePassword, "workerRolePassword");
    Objects.requireNonNull(readerRolePassword, "readerRolePassword");
    Objects.requireNonNull(address, "address");
    Objects.requireNonNull(databaseName, "databaseName");
    Objects.requireNonNull(create, "create");
    Objects.requireNonNull(upgrade, "upgrade");
    Objects.requireNonNull(clock, "clock");
    Objects.requireNonNull(strings, "strings");
    Objects.requireNonNull(language, "language");
  }

  /**
   * @return This database configuration without database creation or
   * upgrades enabled
   */

  public NPDatabaseConfiguration withoutUpgradeOrCreate()
  {
    return new NPDatabaseConfiguration(
      this.ownerRoleName,
      this.ownerRolePassword,
      this.workerRolePassword,
      this.readerRolePassword,
      this.address,
      this.port,
      this.databaseName,
      NPDatabaseCreate.DO_NOT_CREATE_DATABASE,
      NPDatabaseUpgrade.DO_NOT_UPGRADE_DATABASE,
      this.useTLS,
      this.language,
      this.clock,
      this.strings
    );
  }
}
