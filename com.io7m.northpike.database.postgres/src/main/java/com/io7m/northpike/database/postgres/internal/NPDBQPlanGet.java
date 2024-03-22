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

import com.io7m.anethum.api.ParsingException;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PlanGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PlanGetType.Parameters;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.plans.NPPlanDescription;
import org.jooq.DSLContext;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.util.Objects;
import java.util.Optional;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_FORMAT_UNSUPPORTED;
import static com.io7m.northpike.strings.NPStringConstants.FORMAT;

/**
 * Update a plan.
 */

public final class NPDBQPlanGet
  extends NPDBQAbstract<Parameters, Optional<NPPlanDescription>>
  implements PlanGetType
{
  private static final NPDBQueryProviderType.Service<Parameters, Optional<NPPlanDescription>, PlanGetType> SERVICE =
    new NPDBQueryProviderType.Service<>(PlanGetType.class, NPDBQPlanGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPlanGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPPlanDescription> onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPDatabaseException
  {
    final var raw =
      NPDBQPlanGetRaw.getResult(context, parameters.identifier());

    if (raw.isEmpty()) {
      return Optional.empty();
    }

    final var text = raw.get();
    this.setAttribute(FORMAT, text.format().toString());

    final var transaction = this.transaction();
    for (final var parsers : parameters.parsers()) {
      for (final var format : parsers.formats()) {
        if (Objects.equals(format.name(), text.format())) {
          final var bytes =
            text.text().getBytes(StandardCharsets.UTF_8);

          try (var stream = new ByteArrayInputStream(bytes)) {
            final var plan =
              parsers.parse(URI.create("urn:input"), stream);
            return Optional.of(plan);
          } catch (final IOException e) {
            throw NPDatabaseExceptions.ofIOError(
              transaction,
              this.attributes(),
              e
            );
          } catch (final ParsingException e) {
            throw NPDatabaseExceptions.ofParseError(this.attributes(), e);
          }
        }
      }
    }

    throw new NPDatabaseException(
      this.local(ERROR_FORMAT_UNSUPPORTED),
      NPStandardErrorCodes.errorIo(),
      this.attributes(),
      Optional.empty()
    );
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
