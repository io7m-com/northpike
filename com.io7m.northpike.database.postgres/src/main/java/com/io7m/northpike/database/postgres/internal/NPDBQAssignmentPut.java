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


import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static com.io7m.northpike.strings.NPStringConstants.ASSIGNMENT;

/**
 * Update an assignment.
 */

public final class NPDBQAssignmentPut
  extends NPDBQAbstract<NPAssignment, NPDatabaseUnit>
  implements NPDatabaseQueriesAssignmentsType.PutType
{
  private static final Service<NPAssignment, NPDatabaseUnit, PutType> SERVICE =
    new Service<>(PutType.class, NPDBQAssignmentPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentPut(
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
    final NPAssignment assignment)
  {
    this.setAttribute(ASSIGNMENT, assignment.name().toString());

    final var aPlan =
      assignment.plan();

    final var plan =
      context.select(PLANS.P_ID)
        .from(PLANS)
        .where(
          PLANS.P_NAME.eq(aPlan.name().toString())
            .and(PLANS.P_VERSION.eq(Long.valueOf(aPlan.version())))
        );

    final var query =
      context.insertInto(ASSIGNMENTS)
        .set(ASSIGNMENTS.A_NAME, assignment.name().toString())
        .set(ASSIGNMENTS.A_REPOSITORY, assignment.repositoryId())
        .set(ASSIGNMENTS.A_PLAN, plan)
        .onConflictOnConstraint(DSL.name("assignments_name_unique"))
        .doUpdate()
        .set(ASSIGNMENTS.A_NAME, assignment.name().toString())
        .set(ASSIGNMENTS.A_REPOSITORY, assignment.repositoryId())
        .set(ASSIGNMENTS.A_PLAN, plan);

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
