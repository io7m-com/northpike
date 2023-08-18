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
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.GetUnparsedType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.plans.NPPlanIdentifier;
import org.jooq.DSLContext;
import org.jooq.Record3;

import java.nio.charset.Charset;
import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.tables.Plans.PLANS;

/**
 * Retrieve the raw text of a plan.
 */

public final class NPDBQPlanGetRaw
  extends NPDBQAbstract<NPPlanIdentifier, Optional<GetUnparsedType.Result>>
  implements GetUnparsedType
{
  private static final Service<NPPlanIdentifier, Optional<GetUnparsedType.Result>, GetUnparsedType> SERVICE =
    new Service<>(GetUnparsedType.class, NPDBQPlanGetRaw::new);

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

  private static Result mapRecord(
    final Record3<String, String, byte[]> r)
  {
    return new Result(
      r.get(PLANS.P_DATA),
      Charset.forName(r.get(PLANS.P_ENCODING)),
      NPFormatName.of(r.get(PLANS.P_FORMAT))
    );
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  @Override
  protected Optional<Result> onExecute(
    final DSLContext context,
    final NPPlanIdentifier parameters)
    throws NPDatabaseException
  {
    return getResult(context, parameters);
  }

  static Optional<Result> getResult(
    final DSLContext context,
    final NPPlanIdentifier parameters)
  {
    final var condition =
      PLANS.P_NAME.eq(parameters.name().toString())
        .and(PLANS.P_VERSION.eq(Long.valueOf(parameters.version())));

    return context.select(
        PLANS.P_FORMAT,
        PLANS.P_ENCODING,
        PLANS.P_DATA
      ).from(PLANS)
      .where(condition)
      .fetchOptional()
      .map(NPDBQPlanGetRaw::mapRecord);
  }
}
