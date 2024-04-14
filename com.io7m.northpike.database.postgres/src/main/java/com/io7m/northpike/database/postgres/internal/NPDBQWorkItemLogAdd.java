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


import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentWorkItemLogAddType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPWorkItemLogRecord;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;
import org.jooq.impl.SQLDataType;
import org.jooq.postgres.extensions.bindings.HstoreBinding;
import org.jooq.postgres.extensions.types.Hstore;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.NPDBStoredExceptions.serializeExceptionOptional;
import static com.io7m.northpike.database.postgres.internal.Tables.WORK_ITEMS;
import static com.io7m.northpike.database.postgres.internal.Tables.WORK_ITEM_LOGS;

/**
 * Add a line of output to the given work item.
 */

public final class NPDBQWorkItemLogAdd
  extends NPDBQAbstract<NPWorkItemLogRecord, NPDatabaseUnit>
  implements AssignmentWorkItemLogAddType
{
  private static final Service<NPWorkItemLogRecord, NPDatabaseUnit, AssignmentWorkItemLogAddType> SERVICE =
    new Service<>(AssignmentWorkItemLogAddType.class, NPDBQWorkItemLogAdd::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQWorkItemLogAdd(
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
    final NPWorkItemLogRecord logRecord)
  {
    final var identifier =
      logRecord.workItem();

    final var attributesType =
      SQLDataType.OTHER.asConvertedDataType(new HstoreBinding());
    final var attributesField =
      DSL.field("WIL_ATTRIBUTES", attributesType);

    final var item =
      context.select(WORK_ITEMS.WI_ID)
        .from(WORK_ITEMS)
        .where(
          WORK_ITEMS.WI_EXECUTION.eq(identifier.assignmentExecutionId().value())
            .and(WORK_ITEMS.WI_NAME.eq(identifier.planElementName().toString()))
        );

    context.insertInto(WORK_ITEM_LOGS)
      .set(WORK_ITEM_LOGS.WIL_ITEM, item)
      .set(WORK_ITEM_LOGS.WIL_TIME, logRecord.timestamp())
      .set(WORK_ITEM_LOGS.WIL_TEXT, logRecord.message())
      .set(attributesField, Hstore.hstore(logRecord.attributes()))
      .set(WORK_ITEM_LOGS.WIL_EXCEPTION_DATA,
           serializeExceptionOptional(logRecord.exception()))
      .set(WORK_ITEM_LOGS.WIL_EXCEPTION_FORMAT, "CEDARBRIDGE")
      .set(WORK_ITEM_LOGS.WIL_EXCEPTION_VERSION, Integer.valueOf(1))
      .execute();

    return UNIT;
  }
}
