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

import com.io7m.anethum.api.SerializationException;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PutType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.tables.Plans.PLANS;

/**
 * Update a plan.
 */

public final class NPDBQPlanPut
  extends NPDBQAbstract<Parameters, NPDatabaseUnit>
  implements PutType
{
  private static final NPDBQueryProviderType.Service<Parameters, NPDatabaseUnit, PutType> SERVICE =
    new NPDBQueryProviderType.Service<>(PutType.class, NPDBQPlanPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQPlanPut(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPDatabaseException
  {
    final var plan =
      parameters.plan();
    final var identifier =
      plan.identifier();

    final var serializers =
      parameters.serializers();

    try (var output = new ByteArrayOutputStream()) {
      final var serializer =
        serializers.createSerializer(URI.create("urn:out"), output);

      serializer.execute(plan);

      final var charsetName =
        StandardCharsets.UTF_8.name();
      final var data =
        output.toByteArray();

      context.insertInto(PLANS)
        .set(PLANS.P_DATA, data)
        .set(PLANS.P_DESCRIPTION, plan.description())
        .set(PLANS.P_ENCODING, charsetName)
        .set(PLANS.P_FORMAT, serializer.format().toString())
        .set(PLANS.P_NAME, identifier.name().toString())
        .set(PLANS.P_VERSION, Long.valueOf(identifier.version()))
        .onConflictOnConstraint(DSL.name("plans_name_version_unique"))
        .doUpdate()
        .set(PLANS.P_DATA, data)
        .set(PLANS.P_DESCRIPTION, plan.description())
        .set(PLANS.P_ENCODING, charsetName)
        .set(PLANS.P_FORMAT, serializer.format().toString())
        .execute();
    } catch (final IOException e) {
      throw NPDatabaseExceptions.ofIOError(
        this.transaction(),
        this.attributes(),
        e
      );
    } catch (final SerializationException e) {
      throw NPDatabaseExceptions.ofSerializationError(this.attributes(), e);
    }

    return UNIT;
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }

}
