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

import java.util.Objects;
import java.util.Optional;

/**
 * Configuration for the database.
 *
 * @param kind               The underlying SQL database kind
 * @param ownerRoleName      The name of the role that owns the database; used for database setup and migrations
 * @param ownerRolePassword  The password of the role that owns the database
 * @param workerRolePassword The password of the worker role used for normal database operation
 * @param readerRolePassword The password of the role used for read-only database access
 * @param address            The database address
 * @param port               The database port
 * @param databaseName       The database name
 * @param databaseLanguage   The language used for database search indexes
 * @param create             {@code} true if the database should be created
 * @param upgrade            {@code true} if the database schema should be upgraded
 * @param useTLS
 */

public record NPSCDatabase(
  NPSCDatabaseKind kind,
  String ownerRoleName,
  String ownerRolePassword,
  String workerRolePassword,
  Optional<String> readerRolePassword,
  String address,
  int port,
  String databaseName,
  String databaseLanguage,
  boolean create,
  boolean upgrade,
  boolean useTLS)
{
  /**
   * Configuration for the database.
   *
   * @param kind               The underlying SQL database kind
   * @param ownerRoleName      The name of the role that owns the database; used for database setup and migrations
   * @param ownerRolePassword  The password of the role that owns the database
   * @param workerRolePassword The password of the worker role used for normal database operation
   * @param readerRolePassword The password of the role used for read-only database access
   * @param address            The database address
   * @param port               The database port
   * @param databaseName       The database name
   * @param databaseLanguage   The language used for database search indexes
   * @param create             {@code} true if the database should be created
   * @param upgrade            {@code true} if the database schema should be upgraded
   * @param useTLS             {@code true} if TLS should be used to connect to the database
   */

  public NPSCDatabase
  {
    Objects.requireNonNull(kind, "kind");
    Objects.requireNonNull(ownerRoleName, "ownerRoleName");
    Objects.requireNonNull(ownerRolePassword, "ownerRolePassword");
    Objects.requireNonNull(workerRolePassword, "workerRolePassword");
    Objects.requireNonNull(readerRolePassword, "readerRolePassword");
    Objects.requireNonNull(address, "address");
    Objects.requireNonNull(databaseName, "databaseName");
    Objects.requireNonNull(databaseLanguage, "databaseLanguage");
  }
}
