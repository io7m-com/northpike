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


import com.io7m.anethum.api.ParseStatusType;
import com.io7m.anethum.api.ParsingException;
import com.io7m.anethum.api.SerializationException;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import org.jooq.exception.DataAccessException;
import org.postgresql.util.PSQLException;
import org.postgresql.util.ServerErrorMessage;

import java.io.IOException;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.SortedMap;
import java.util.TreeMap;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_IO;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;


/**
 * Functions to handle database exceptions.
 */

public final class NPDatabaseExceptions
{
  private NPDatabaseExceptions()
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

  @SafeVarargs
  public static NPDatabaseException handleDatabaseException(
    final NPDatabaseTransaction transaction,
    final DataAccessException e,
    final Map.Entry<String, String>... attributes)
  {
    final var tm = new TreeMap<String, String>();
    for (final var entry : attributes) {
      tm.put(entry.getKey(), entry.getValue());
    }
    return handleDatabaseException(transaction, e, tm);
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

  public static NPDatabaseException handleDatabaseException(
    final NPDatabaseTransaction transaction,
    final DataAccessException e,
    final SortedMap<String, String> attributes)
  {
    final var m = e.getMessage();

    /*
     * See https://www.postgresql.org/docs/current/errcodes-appendix.html
     * for all of these numeric codes.
     */

    final NPDatabaseException result = switch (e.sqlState()) {

      /*
       * foreign_key_violation
       */

      case "23502" -> integrityViolation(transaction, e, attributes, m);

      /*
       * foreign_key_violation
       */

      case "23503" -> foreignKeyViolation(transaction, e, attributes, m);

      /*
       * unique_violation
       */

      case "23505" -> handleUniqueViolation(e, attributes, m);

      /*
       * PostgreSQL: character_not_in_repertoire
       */

      case "22021" -> handleCharacterEncoding(e, attributes);

      /*
       * insufficient_privilege
       */

      case "42501" -> {
        yield new NPDatabaseException(
          m,
          e,
          NPStandardErrorCodes.errorOperationNotPermitted(),
          attributes,
          Optional.empty()
        );
      }

      default -> {
        yield new NPDatabaseException(
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
    } catch (final NPDatabaseException ex) {
      result.addSuppressed(ex);
    }
    return result;
  }

  private static NPDatabaseException integrityViolation(
    final NPDatabaseTransaction transaction,
    final DataAccessException e,
    final SortedMap<String, String> attributes,
    final String m)
  {
    final String column =
      findPSQLException(e)
        .flatMap(z -> Optional.ofNullable(z.getServerErrorMessage()))
        .map(ServerErrorMessage::getColumn)
        .orElse("");

    return switch (column.toUpperCase(Locale.ROOT)) {
      case "R_PROVIDER", "AE_COMMIT" -> {
        yield new NPDatabaseException(
          transaction.localize(ERROR_NONEXISTENT),
          e,
          NPStandardErrorCodes.errorNonexistent(),
          attributes,
          Optional.empty()
        );
      }

      default -> {
        yield new NPDatabaseException(
          m,
          e,
          NPStandardErrorCodes.errorSql(),
          attributes,
          Optional.empty()
        );
      }
    };
  }

  private static NPDatabaseException handleCharacterEncoding(
    final DataAccessException e,
    final SortedMap<String, String> attributes)
  {
    final String message =
      findPSQLException(e)
        .flatMap(z -> Optional.ofNullable(z.getServerErrorMessage()))
        .map(ServerErrorMessage::getMessage)
        .orElseGet(e::getMessage);

    return new NPDatabaseException(
      message,
      e,
      NPStandardErrorCodes.errorProtocol(),
      attributes,
      Optional.empty()
    );
  }

  private static NPDatabaseException handleUniqueViolation(
    final DataAccessException e,
    final SortedMap<String, String> attributes,
    final String m)
  {
    final String constraint =
      findPSQLException(e)
        .flatMap(z -> Optional.ofNullable(z.getServerErrorMessage()))
        .map(ServerErrorMessage::getConstraint)
        .orElse("");

    return switch (constraint.toUpperCase(Locale.ROOT)) {
      case "AGENTS_ACCESS_KEY_UNIQUE" -> {
        yield new NPDatabaseException(
          m,
          e,
          NPStandardErrorCodes.errorDuplicate(),
          attributes,
          Optional.empty()
        );
      }

      default -> {
        yield new NPDatabaseException(
          m,
          e,
          NPStandardErrorCodes.errorSql(),
          attributes,
          Optional.empty()
        );
      }
    };
  }

  private static Optional<PSQLException> findPSQLException(
    final DataAccessException e)
  {
    var x = e.getCause();
    while (x != null) {
      if (x instanceof final PSQLException xx) {
        return Optional.of(xx);
      }
      x = x.getCause();
    }
    return Optional.empty();
  }

  private static NPDatabaseException foreignKeyViolation(
    final NPDatabaseTransaction transaction,
    final DataAccessException e,
    final SortedMap<String, String> attributes,
    final String m)
  {
    final Optional<PSQLException> ep = findPSQLException(e);
    if (ep.isPresent()) {
      return foreignKeyPSQL(transaction, e, attributes, m, ep.get());
    }

    return new NPDatabaseException(
      m,
      e,
      NPStandardErrorCodes.errorSql(),
      attributes,
      Optional.empty()
    );
  }

  private static NPDatabaseException foreignKeyPSQL(
    final NPDatabaseTransaction transaction,
    final Exception root,
    final SortedMap<String, String> attributes,
    final String m,
    final PSQLException actual)
  {
    final var constraint =
      Optional.ofNullable(actual.getServerErrorMessage())
        .flatMap(x -> Optional.ofNullable(x.getConstraint()))
        .map(x -> x.toUpperCase(Locale.ROOT))
        .orElse("");

    return switch (constraint) {
      case "REPOSITORY_COMMITS_REPOSITORY_EXISTS" -> {
        yield new NPDatabaseException(
          transaction.localize(ERROR_NONEXISTENT),
          root,
          NPStandardErrorCodes.errorNonexistent(),
          attributes,
          Optional.empty()
        );
      }
      default -> {
        yield new NPDatabaseException(
          m,
          root,
          NPStandardErrorCodes.errorSql(),
          attributes,
          Optional.empty()
        );
      }
    };
  }

  static NPDatabaseException ofIOError(
    final NPDatabaseTransaction transaction,
    final Map<String, String> attributes,
    final IOException e)
  {
    return new NPDatabaseException(
      transaction.localize(ERROR_IO),
      e,
      NPStandardErrorCodes.errorIo(),
      attributes,
      Optional.empty()
    );
  }

  static NPDatabaseException ofSerializationError(
    final Map<String, String> attributes,
    final SerializationException e)
  {
    return new NPDatabaseException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorIo(),
      attributes,
      Optional.empty()
    );
  }

  static NPDatabaseException ofParseError(
    final Map<String, String> attributes,
    final ParsingException e)
  {
    final var newAttributes = new TreeMap<>(attributes);
    final var errors = e.statusValues();
    for (int index = 0; index < errors.size(); ++index) {
      final var status = errors.get(index);
      final var name = "Status %d".formatted(Integer.valueOf(index));
      newAttributes.put(name, formatStatus(status));
    }

    return new NPDatabaseException(
      e.getMessage(),
      e,
      NPStandardErrorCodes.errorIo(),
      newAttributes,
      Optional.empty()
    );
  }

  private static String formatStatus(
    final ParseStatusType status)
  {
    return String.format(
      "%d:%d %s %s",
      Integer.valueOf(status.lexical().line()),
      Integer.valueOf(status.lexical().column()),
      status.errorCode(),
      status.message()
    );
  }
}
