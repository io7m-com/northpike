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

package com.io7m.northpike.database.postgres.internal;


import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.model.NPStandardErrorCodes;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.context.Context;

import java.sql.Connection;
import java.sql.SQLException;
import java.time.Duration;
import java.time.OffsetDateTime;
import java.util.Map;
import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.NPDatabaseTransaction.CloseBehavior.ON_CLOSE_DO_NOTHING;
import static java.util.Objects.requireNonNullElse;

record NPDatabaseConnection(
  NPDatabase database,
  Connection connection,
  OffsetDateTime timeStart,
  NPDatabaseRole role,
  Span connectionSpan)
  implements NPDatabaseConnectionType
{
  @Override
  public NPDatabaseTransactionType openTransaction()
    throws NPDatabaseException
  {
    return this.openTransactionWithCloseBehavior(ON_CLOSE_DO_NOTHING);
  }

  NPDatabaseTransaction openTransactionWithCloseBehavior(
    final NPDatabaseTransaction.CloseBehavior closeBehavior)
    throws NPDatabaseException
  {
    final var transactionSpan =
      this.database.tracer()
        .spanBuilder("NPDatabaseTransaction")
        .setParent(Context.current().with(this.connectionSpan))
        .startSpan();

    try {
      final var t =
        new NPDatabaseTransaction(
          closeBehavior,
          this,
          transactionSpan
        );

      this.database.counterTransactions().add(1L);
      t.setRole(this.role);
      t.commit();
      return t;
    } catch (final SQLException e) {
      transactionSpan.recordException(e);
      transactionSpan.end();
      throw new NPDatabaseException(
        requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
        e,
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    }
  }

  @Override
  public void close()
    throws NPDatabaseException
  {
    try {
      final var timeNow = OffsetDateTime.now();
      this.database.setConnectionTimeNow(
        Duration.between(this.timeStart, timeNow).toNanos()
      );

      if (!this.connection.isClosed()) {
        this.connection.close();
      }
    } catch (final SQLException e) {
      this.connectionSpan.recordException(e);
      throw new NPDatabaseException(
        requireNonNullElse(e.getMessage(), e.getClass().getSimpleName()),
        e,
        NPStandardErrorCodes.errorSql(),
        Map.of(),
        Optional.empty()
      );
    } finally {
      this.connectionSpan.end();
    }
  }
}
