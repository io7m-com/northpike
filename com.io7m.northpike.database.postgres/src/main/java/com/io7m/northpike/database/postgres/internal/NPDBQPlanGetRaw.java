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


import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PlanGetUnparsedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.plans.NPPlanDescriptionUnparsed;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.model.plans.NPPlanName;
import org.jooq.DSLContext;

import java.nio.charset.Charset;
import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.tables.Plans.PLANS;

/**
 * Retrieve the raw text of a plan.
 */

public final class NPDBQPlanGetRaw
  extends NPDBQAbstract<NPPlanIdentifier, Optional<NPPlanDescriptionUnparsed>>
  implements PlanGetUnparsedType
{
  private static final Service<NPPlanIdentifier, Optional<NPPlanDescriptionUnparsed>, PlanGetUnparsedType> SERVICE =
    new Service<>(PlanGetUnparsedType.class, NPDBQPlanGetRaw::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPlanGetRaw(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected Optional<NPPlanDescriptionUnparsed> onExecute(
    final DSLContext context,
    final NPPlanIdentifier parameters)
    throws NPDatabaseException
  {
    return getResult(context, parameters);
  }

  static Optional<NPPlanDescriptionUnparsed> getResult(
    final DSLContext context,
    final NPPlanIdentifier parameters)
  {
    final var condition =
      PLANS.P_NAME.eq(parameters.name().toString())
        .and(PLANS.P_VERSION.eq(Long.valueOf(parameters.version())));

    return context.select(
        PLANS.P_NAME,
        PLANS.P_VERSION,
        PLANS.P_FORMAT,
        PLANS.P_ENCODING,
        PLANS.P_DATA
      ).from(PLANS)
      .where(condition)
      .fetchOptional()
      .map(NPDBQPlanGetRaw::mapRecord);
  }

  private static NPPlanDescriptionUnparsed mapRecord(
    final org.jooq.Record record)
  {
    final var data =
      record.get(PLANS.P_DATA);
    final var chars =
      Charset.forName(record.get(PLANS.P_ENCODING));

    return new NPPlanDescriptionUnparsed(
      new NPPlanIdentifier(
        NPPlanName.of(record.get(PLANS.P_NAME)),
        record.get(PLANS.P_VERSION).longValue()
      ),
      NPFormatName.of(record.get(PLANS.P_FORMAT)),
      new String(data, chars)
    );
  }
}
