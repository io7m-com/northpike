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


package com.io7m.northpike.server.internal.users;

import com.io7m.idstore.user_client.api.IdUClientException;
import com.io7m.idstore.user_client.api.IdUClientSynchronousType;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.strings.NPStringConstantType;

import java.net.URI;
import java.util.UUID;

/**
 * The context used for command execution.
 */

public interface NPUserCommandContextType
{
  /**
   * Create a new idstore user client.
   *
   * @return The client
   */

  IdUClientSynchronousType createIdstoreClient()
    throws IdUClientException, InterruptedException;

  /**
   * Signal that the current command execution requires authentication, and
   * raise an exception if not currently authenticated.
   *
   * @return The authenticated user
   *
   * @throws NPException On errors
   */

  NPUser onAuthenticationRequire()
    throws NPException;

  /**
   * Indicate that authentication completed successfully.
   *
   * @param user The user
   */

  void onAuthenticationComplete(
    UUID user);

  /**
   * Fail with an error.
   *
   * @param message   The error message
   * @param errorCode The error code
   *
   * @return The exception
   */

  NPException fail(
    NPStringConstantType message,
    NPErrorCode errorCode);

  /**
   * Fail with an error.
   *
   * @param cause     The cause
   * @param message   The error message
   * @param errorCode The error code
   *
   * @return The exception
   */

  NPException fail(
    Exception cause,
    NPStringConstantType message,
    NPErrorCode errorCode);

  /**
   * Indicate that the current user wants to disconnect.
   */

  void disconnect();

  /**
   * @return A new database connection
   *
   * @throws NPException On errors
   */

  NPDatabaseConnectionType databaseConnection()
    throws NPException;

  /**
   * @return The configured idstore login URI
   */

  URI idstoreLoginURI();
}
