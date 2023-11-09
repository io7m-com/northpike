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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import org.jooq.exception.DataAccessException;
import org.jooq.exception.IntegrityConstraintViolationException;

import java.util.Optional;
import java.util.TreeMap;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_DATABASE_FOREIGN_INTEGRITY;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_DATABASE_FOREIGN_INTEGRITY_REMEDIATE;

/**
 * Functions to handle database exceptions.
 */

public final class NPASExceptions
{
  private NPASExceptions()
  {

  }

  /**
   * Handle a data access exception.
   *
   * @param transaction The transaction
   * @param e           The exception
   * @param attributes  The attributes
   *
   * @return The resulting exception
   */

  public static NPAgentDatabaseException handleDatabaseException(
    final NPASTransaction transaction,
    final DataAccessException e,
    final TreeMap<String, String> attributes)
  {
    final var m =
      e.getMessage();

    final var result =
      switch (e) {
        case final IntegrityConstraintViolationException ie -> {
          yield handleDatabaseIntegrityException(transaction, ie, attributes);
        }
        default -> {
          yield new NPAgentDatabaseException(
            m,
            e,
            NPStandardErrorCodes.errorSql(),
            attributes,
            Optional.empty()
          );
        }
      };

    try {
      transaction.rollback();
    } catch (final NPAgentDatabaseException ex) {
      result.addSuppressed(ex);
    }
    return result;
  }

  private static NPAgentDatabaseException handleDatabaseIntegrityException(
    final NPASTransaction transaction,
    final IntegrityConstraintViolationException ie,
    final TreeMap<String, String> attributes)
  {
    return new NPAgentDatabaseException(
      transaction.localize(ERROR_DATABASE_FOREIGN_INTEGRITY),
      ie,
      NPStandardErrorCodes.errorSqlForeignKey(),
      attributes,
      Optional.of(
        transaction.localize(ERROR_DATABASE_FOREIGN_INTEGRITY_REMEDIATE)
      )
    );
  }
}
