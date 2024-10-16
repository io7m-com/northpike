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


package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPErrorCode;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.model.agents.NPAgentDescription;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.agents.NPAgentKeyID;
import com.io7m.northpike.strings.NPStringConstantType;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.util.Optional;

/**
 * The context used for command execution.
 */

public interface NPAgentCommandContextType
  extends NPAgentAccessType
{
  /**
   * @return The service directory
   */

  RPServiceDirectoryType services();

  /**
   * Signal that the current command execution requires authentication, and
   * raise an exception if not currently authenticated.
   *
   * @return The ID of the authenticated agent
   *
   * @throws NPException On errors
   */

  NPAgentID onAuthenticationRequire()
    throws NPException;

  /**
   * Indicate that authentication completed successfully.
   *
   * @param agent The agent
   */

  void onAuthenticationComplete(NPAgentDescription agent);

  /**
   * Indicate that authentication failed.
   *
   * @param keyID   The key ID, if any
   * @param message The message
   */

  void onAuthenticationFailed(
    Optional<NPAgentKeyID> keyID,
    NPStringConstantType message);

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
   * Indicate that the current agent wants to disconnect.
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
   * @param role The database role
   *
   * @return A new database transaction
   *
   * @throws NPException On errors
   * @see com.io7m.northpike.database.api.NPDatabaseType#transaction(NPDatabaseRole)
   */

  NPDatabaseTransactionType transaction(NPDatabaseRole role)
    throws NPException;

  /**
   * @return A new database transaction
   *
   * @throws NPException On errors
   * @see com.io7m.northpike.database.api.NPDatabaseType#transaction(NPDatabaseRole)
   */

  default NPDatabaseTransactionType transaction()
    throws NPException
  {
    return this.transaction(NPDatabaseRole.NORTHPIKE);
  }

  /**
   * Indicate that the status of a work item handled by this agent has
   * changed.
   *
   * @param identifier The work item
   * @param status     The new status
   */

  void onWorkItemStatusChanged(
    NPWorkItemIdentifier identifier,
    NPWorkItemStatus status);

  /**
   * Indicate that a work item has been accepted.
   *
   * @param identifier The work item
   *
   * @throws NPException On errors
   */

  void onWorkItemAccepted(
    NPWorkItemIdentifier identifier)
    throws NPException;

  /**
   * @return The address of the remote peer
   */

  String sourceAddress();
}
