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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.WorkItemGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.database.postgres.internal.enums.WorkItemStatusT;
import com.io7m.northpike.model.NPAgentID;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.model.NPWorkItemStatus;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import org.jooq.DSLContext;
import org.jooq.Record4;

import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.Tables.WORK_ITEMS;

/**
 * Retrieve a work item.
 */

public final class NPDBQWorkItemGet
  extends NPDBQAbstract<NPWorkItemIdentifier, Optional<NPWorkItem>>
  implements WorkItemGetType
{
  private static final Service<NPWorkItemIdentifier, Optional<NPWorkItem>, WorkItemGetType> SERVICE =
    new Service<>(WorkItemGetType.class, NPDBQWorkItemGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQWorkItemGet(
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
  protected Optional<NPWorkItem> onExecute(
    final DSLContext context,
    final NPWorkItemIdentifier id)
    throws NPDatabaseException
  {
    return context.select(
        WORK_ITEMS.WI_EXECUTION,
        WORK_ITEMS.WI_AGENT,
        WORK_ITEMS.WI_NAME,
        WORK_ITEMS.WI_STATUS)
      .from(WORK_ITEMS)
      .where(
        WORK_ITEMS.WI_EXECUTION.eq(id.assignmentExecutionId().value())
          .and(WORK_ITEMS.WI_NAME.eq(id.planElementName().toString()))
      ).fetchOptional()
      .map(NPDBQWorkItemGet::mapRecord);
  }

  private static NPWorkItem mapRecord(
    final Record4<UUID, UUID, String, WorkItemStatusT> r)
  {
    return new NPWorkItem(
      new NPWorkItemIdentifier(
        new NPAssignmentExecutionID(r.get(WORK_ITEMS.WI_EXECUTION)),
        new RDottedName(r.get(WORK_ITEMS.WI_NAME))
      ),
      Optional.ofNullable(r.get(WORK_ITEMS.WI_AGENT))
        .map(NPAgentID::new),
      ofStatus(r.get(WORK_ITEMS.WI_STATUS))
    );
  }

  private static NPWorkItemStatus ofStatus(
    final WorkItemStatusT status)
  {
    return switch (status) {
      case WORK_ITEM_ACCEPTED -> NPWorkItemStatus.WORK_ITEM_ACCEPTED;
      case WORK_ITEM_CREATED -> NPWorkItemStatus.WORK_ITEM_CREATED;
      case WORK_ITEM_FAILED -> NPWorkItemStatus.WORK_ITEM_FAILED;
      case WORK_ITEM_RUNNING -> NPWorkItemStatus.WORK_ITEM_RUNNING;
      case WORK_ITEM_SUCCEEDED -> NPWorkItemStatus.WORK_ITEM_SUCCEEDED;
    };
  }
}
