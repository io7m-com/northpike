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


import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.ExecutionLogAddType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;
import org.jooq.impl.SQLDataType;
import org.jooq.postgres.extensions.bindings.HstoreBinding;
import org.jooq.postgres.extensions.types.Hstore;

import java.time.OffsetDateTime;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.NPDBStoredExceptions.serializeExceptionOptional;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENT_EXECUTION_LOGS;

/**
 * Add a line of output to the assignment execution.
 */

public final class NPDBQAssignmentExecutionLogAdd
  extends NPDBQAbstract<ExecutionLogAddType.Parameters, NPDatabaseUnit>
  implements ExecutionLogAddType
{
  private static final Service<ExecutionLogAddType.Parameters, NPDatabaseUnit, ExecutionLogAddType> SERVICE =
    new Service<>(
      ExecutionLogAddType.class,
      NPDBQAssignmentExecutionLogAdd::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentExecutionLogAdd(
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
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final Parameters parameters)
  {
    final var time =
      OffsetDateTime.now(
        this.transaction()
          .connection()
          .database()
          .clock()
      );

    final var attributesType =
      SQLDataType.OTHER.asConvertedDataType(new HstoreBinding());
    final var attributesField =
      DSL.field("AEL_ATTRIBUTES", attributesType);

    context.insertInto(ASSIGNMENT_EXECUTION_LOGS)
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_ID, parameters.execution().value())
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_MESSAGE, parameters.message())
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_TIME, time)
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_INDEX, parameters.index())
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_TYPE, parameters.type())
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_DATA,
           serializeExceptionOptional(parameters.exception()))
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_FORMAT, "CEDARBRIDGE")
      .set(ASSIGNMENT_EXECUTION_LOGS.AEL_EXCEPTION_VERSION, Integer.valueOf(1))
      .set(attributesField, Hstore.valueOf(parameters.attributes()))
      .onDuplicateKeyIgnore()
      .execute();

    return UNIT;
  }
}
