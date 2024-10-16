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
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType.AssignmentGetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import org.jooq.DSLContext;
import org.jooq.Record;

import java.util.Optional;

import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static com.io7m.northpike.model.assignments.NPAssignmentScheduleNone.SCHEDULE_NONE;

/**
 * Retrieve an assignment.
 */

public final class NPDBQAssignmentGet
  extends NPDBQAbstract<NPAssignmentName, Optional<NPAssignment>>
  implements AssignmentGetType
{
  private static final Service<NPAssignmentName, Optional<NPAssignment>, AssignmentGetType> SERVICE =
    new Service<>(AssignmentGetType.class, NPDBQAssignmentGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQAssignmentGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  @Override
  protected Optional<NPAssignment> onExecute(
    final DSLContext context,
    final NPAssignmentName name)
    throws NPDatabaseException
  {
    return context.select(
        ASSIGNMENTS.A_NAME,
        ASSIGNMENTS.A_REPOSITORY,
        ASSIGNMENTS.A_SCHEDULE,
        ASSIGNMENTS.A_SCHEDULE_COMMIT_AGE_CUTOFF,
        PLANS.P_NAME,
        PLANS.P_VERSION
      ).from(ASSIGNMENTS)
      .join(PLANS)
      .on(ASSIGNMENTS.A_PLAN.eq(PLANS.P_ID))
      .where(ASSIGNMENTS.A_NAME.eq(name.value().value()))
      .fetchOptional()
      .map(NPDBQAssignmentGet::mapRecord);
  }

  private static NPAssignment mapRecord(
    final org.jooq.Record r)
  {
    return new NPAssignment(
      NPAssignmentName.of(r.get(ASSIGNMENTS.A_NAME)),
      new NPRepositoryID(r.get(ASSIGNMENTS.A_REPOSITORY)),
      NPPlanIdentifier.of(
        r.get(PLANS.P_NAME),
        r.<Long>get(PLANS.P_VERSION).longValue()
      ),
      mapSchedule(r)
    );
  }

  static NPAssignmentScheduleType mapSchedule(
    final Record r)
  {
    return switch (r.get(ASSIGNMENTS.A_SCHEDULE)) {
      case ASSIGNMENT_SCHEDULE_NONE -> SCHEDULE_NONE;
      case ASSIGNMENT_SCHEDULE_HOURLY_HASHED ->
        new NPAssignmentScheduleHourlyHashed(
          r.get(ASSIGNMENTS.A_SCHEDULE_COMMIT_AGE_CUTOFF)
        );
    };
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }
}
