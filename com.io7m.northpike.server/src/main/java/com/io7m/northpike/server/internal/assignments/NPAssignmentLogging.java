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


package com.io7m.northpike.server.internal.assignments;

import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionLogAddType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentExecutionLogAddType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.seltzer.api.SStructuredErrorType;

import java.util.Map;
import java.util.Optional;

import static java.util.Objects.requireNonNullElse;

/**
 * Functions to log text to the database during assignment execution.
 */

public final class NPAssignmentLogging
{
  private NPAssignmentLogging()
  {

  }

  /**
   * Record the text of an exception.
   *
   * @param transaction The transaction
   * @param eventIndex  The event index
   * @param executionId The execution ID
   * @param e           The exception
   *
   * @throws NPDatabaseException On errors
   */

  public static void recordException(
    final NPDatabaseTransactionType transaction,
    final NPAssignmentExecutionID executionId,
    final long eventIndex,
    final Throwable e)
    throws NPDatabaseException
  {
    final Map<String, String> attributes;
    if (e instanceof final SStructuredErrorType<?> s) {
      attributes = s.attributes();
    } else {
      attributes = Map.of();
    }

    transaction.queries(AssignmentExecutionLogAddType.class)
      .execute(
        new Parameters(
          executionId,
          eventIndex,
          "EXCEPTION",
          requireNonNullElse(e.getMessage(), e.getClass().getCanonicalName()),
          attributes,
          Optional.of(NPStoredException.ofException(e))
        )
      );
  }

  /**
   * Record the given text.
   *
   * @param transaction The transaction
   * @param eventIndex  The event index
   * @param executionId The execution ID
   * @param text        The text
   *
   * @throws NPDatabaseException On errors
   */

  public static void recordInfoText(
    final NPDatabaseTransactionType transaction,
    final NPAssignmentExecutionID executionId,
    final long eventIndex,
    final String text)
    throws NPDatabaseException
  {
    transaction.queries(AssignmentExecutionLogAddType.class)
      .execute(new Parameters(
        executionId,
        eventIndex,
        "INFO",
        text,
        Map.of(),
        Optional.empty())
      );
  }

  /**
   * Record the given text.
   *
   * @param transaction The transaction
   * @param eventIndex  The event index
   * @param executionId The execution ID
   * @param text        The text
   *
   * @throws NPDatabaseException On errors
   */

  public static void recordErrorText(
    final NPDatabaseTransactionType transaction,
    final NPAssignmentExecutionID executionId,
    final long eventIndex,
    final String text)
    throws NPDatabaseException
  {
    transaction.queries(AssignmentExecutionLogAddType.class)
      .execute(new Parameters(
        executionId,
        eventIndex,
        "ERROR",
        text,
        Map.of(),
        Optional.empty())
      );
  }
}
