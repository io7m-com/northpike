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


import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.database.postgres.internal.enums.WorkItemStatusT;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.model.agents.NPAgentID;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.WORK_ITEMS;

/**
 * Update a work item.
 */

public final class NPDBQWorkItemPut
  extends NPDBQAbstract<NPWorkItem, NPDatabaseUnit>
  implements NPDatabaseQueriesAssignmentsType.WorkItemPutType
{
  private static final Service<NPWorkItem, NPDatabaseUnit, WorkItemPutType> SERVICE =
    new Service<>(WorkItemPutType.class, NPDBQWorkItemPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQWorkItemPut(
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
    final NPWorkItem workItem)
  {
    final var identifier =
      workItem.identifier();
    final var agent =
      workItem.selectedAgent()
        .map(NPAgentID::value)
        .orElse(null);

    final var status =
      switch (workItem.status()) {
        case WORK_ITEM_ACCEPTED -> WorkItemStatusT.WORK_ITEM_ACCEPTED;
        case WORK_ITEM_FAILED -> WorkItemStatusT.WORK_ITEM_FAILED;
        case WORK_ITEM_CREATED -> WorkItemStatusT.WORK_ITEM_CREATED;
        case WORK_ITEM_RUNNING -> WorkItemStatusT.WORK_ITEM_RUNNING;
        case WORK_ITEM_SUCCEEDED -> WorkItemStatusT.WORK_ITEM_SUCCEEDED;
      };

    final var query =
      context.insertInto(WORK_ITEMS)
        .set(WORK_ITEMS.WI_EXECUTION, identifier.assignmentExecutionId().value())
        .set(WORK_ITEMS.WI_AGENT, agent)
        .set(WORK_ITEMS.WI_NAME, identifier.planElementName().toString())
        .set(WORK_ITEMS.WI_STATUS, status)
        .onConflictOnConstraint(DSL.name("work_items_assignment_item_unique"))
        .doUpdate()
        .set(WORK_ITEMS.WI_EXECUTION, identifier.assignmentExecutionId().value())
        .set(WORK_ITEMS.WI_AGENT, agent)
        .set(WORK_ITEMS.WI_NAME, identifier.planElementName().toString())
        .set(WORK_ITEMS.WI_STATUS, status);

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
