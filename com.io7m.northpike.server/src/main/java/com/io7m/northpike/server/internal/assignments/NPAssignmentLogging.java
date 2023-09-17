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
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionLogAddType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionLogAddType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.seltzer.api.SStructuredErrorType;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Map;
import java.util.UUID;

import static java.nio.charset.StandardCharsets.UTF_8;

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
   * @param executionId The execution ID
   * @param e           The exception
   *
   * @throws NPDatabaseException On errors
   */

  public static void recordExceptionText(
    final NPDatabaseTransactionType transaction,
    final UUID executionId,
    final Throwable e)
    throws NPDatabaseException
  {
    final var bytes = new ByteArrayOutputStream();
    try (var writer = new PrintStream(bytes, true, UTF_8)) {
      e.printStackTrace(writer);
      writer.flush();

      final Map<String, String> attributes;
      if (e instanceof final SStructuredErrorType<?> s) {
        attributes = s.attributes();
      } else {
        attributes = Map.of();
      }

      transaction.queries(ExecutionLogAddType.class)
        .execute(
          new Parameters(
            executionId,
            "EXCEPTION",
            bytes.toString(UTF_8),
            attributes
          )
        );
    }
  }

  /**
   * Record the given text.
   *
   * @param transaction The transaction
   * @param executionId The execution ID
   * @param text        The text
   *
   * @throws NPDatabaseException On errors
   */

  public static void recordInfoText(
    final NPDatabaseTransactionType transaction,
    final UUID executionId,
    final String text)
    throws NPDatabaseException
  {
    transaction.queries(ExecutionLogAddType.class)
      .execute(new Parameters(executionId, "INFO", text, Map.of()));
  }

  /**
   * Record the given text.
   *
   * @param transaction The transaction
   * @param executionId The execution ID
   * @param text        The text
   *
   * @throws NPDatabaseException On errors
   */

  public static void recordErrorText(
    final NPDatabaseTransactionType transaction,
    final UUID executionId,
    final String text)
    throws NPDatabaseException
  {
    transaction.queries(ExecutionLogAddType.class)
      .execute(new Parameters(executionId, "ERROR", text, Map.of()));
  }
}
