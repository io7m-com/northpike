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


package com.io7m.northpike.shell.commons;

import com.io7m.repetoir.core.RPServiceType;

import java.util.UUID;

/**
 * A confirmation service. Stores records of operations that have to be
 * confirmed before they can be executed.
 */

public interface NPShellConfirmationServiceType
  extends RPServiceType
{
  /**
   * Confirm, remove, and execute the operation with the given ID.
   *
   * @param value The ID
   *
   * @throws Exception                  On errors
   * @throws NPShellConfirmationMissing On missing confirmation values
   */

  void confirm(UUID value)
    throws Exception, NPShellConfirmationMissing;

  /**
   * Register an operation that needs to be confirmed.
   *
   * @param request The operation
   *
   * @return The confirmation requirement
   */

  NPShellConfirmationRequired register(
    NPShellConfirmationRequest request);

  /**
   * Set the next confirmation ID that will be issued.
   *
   * @param confirmationId The confirmation ID
   */

  void setNextConfirmationId(
    UUID confirmationId);
}
