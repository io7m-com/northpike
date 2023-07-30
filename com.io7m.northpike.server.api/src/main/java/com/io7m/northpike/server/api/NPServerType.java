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

import com.io7m.idstore.model.IdName;
import com.io7m.northpike.database.api.NPDatabaseType;

import java.util.UUID;

/**
 * The type of servers.
 */

public interface NPServerType extends AutoCloseable
{
  /**
   * Start the server instance. Can be called multiple times redundantly, and
   * can be called before or after #close() has been called.
   *
   * @throws NPServerException On errors
   */

  void start()
    throws NPServerException;

  /**
   * @return The server's database instance
   */

  NPDatabaseType database();

  /**
   * @return The server's associated configuration
   */

  NPServerConfiguration configuration();

  /**
   * @return {@code true} if the server is closed
   *
   * @see #start()
   * @see #close()
   */

  boolean isClosed();

  /**
   * <p>Do the work necessary to set up a server instance (such as initializing
   * and/or upgrading the database) but do not actually start the instance. A
   * user with the given ID will be marked as the administrator and assigned all
   * available security roles.</p>
   * <p>The given name is simply informative; it will be replaced by the
   * name in the identity server the first time the user logs in.</p>
   *
   * @param adminId   The admin ID
   * @param adminName The name
   *
   * @throws NPServerException On errors
   */

  void setUserAsAdmin(
    UUID adminId,
    IdName adminName)
    throws NPServerException;

  @Override
  void close()
    throws NPServerException;
}
