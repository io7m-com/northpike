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
import com.io7m.northpike.database.postgres.internal.enums.AssignmentScheduleT;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleType;
import org.jooq.DSLContext;
import org.jooq.impl.DSL;

import java.time.OffsetDateTime;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.ASSIGNMENTS;
import static com.io7m.northpike.database.postgres.internal.Tables.PLANS;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentScheduleT.ASSIGNMENT_SCHEDULE_HOURLY_HASHED;
import static com.io7m.northpike.database.postgres.internal.enums.AssignmentScheduleT.ASSIGNMENT_SCHEDULE_NONE;
import static com.io7m.northpike.strings.NPStringConstants.ASSIGNMENT;
import static java.util.Map.entry;

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
        .set(ASSIGNMENTS.A_REPOSITORY, assignment.repositoryId().value())
        .set(ASSIGNMENTS.A_PLAN, plan)
        .set(ASSIGNMENTS.A_SCHEDULE, mapScheduleType(assignment.schedule()))
        .set(ASSIGNMENTS.A_SCHEDULE_COMMIT_AGE_CUTOFF, mapScheduleCommitAgeCutoff(assignment.schedule()))
        .onConflictOnConstraint(DSL.name("assignments_name_unique"))
        .doUpdate()
        .set(ASSIGNMENTS.A_NAME, assignment.name().toString())
        .set(ASSIGNMENTS.A_REPOSITORY, assignment.repositoryId().value())
        .set(ASSIGNMENTS.A_PLAN, plan)
        .set(ASSIGNMENTS.A_SCHEDULE, mapScheduleType(assignment.schedule()))
        .set(ASSIGNMENTS.A_SCHEDULE_COMMIT_AGE_CUTOFF, mapScheduleCommitAgeCutoff(assignment.schedule()));

    recordQuery(query);
    query.execute();

    this.auditEventPut(
      context,
      "ASSIGNMENT_PUT",
      entry("ASSIGNMENT", assignment.name().toString())
    );
    return UNIT;
  }

  private static OffsetDateTime mapScheduleCommitAgeCutoff(
    final NPAssignmentScheduleType schedule)
  {
    if (schedule instanceof final NPAssignmentScheduleHourlyHashed hashed) {
      return hashed.commitAgeCutoff();
    }
    if (schedule instanceof NPAssignmentScheduleNone) {
      return null;
    }
    throw new IllegalStateException(
      "Unrecognized schedule type: %s".formatted(schedule)
    );
  }

  private static AssignmentScheduleT mapScheduleType(
    final NPAssignmentScheduleType schedule)
  {
    if (schedule instanceof NPAssignmentScheduleHourlyHashed) {
      return ASSIGNMENT_SCHEDULE_HOURLY_HASHED;
    }
    if (schedule instanceof NPAssignmentScheduleNone) {
      return ASSIGNMENT_SCHEDULE_NONE;
    }

    throw new IllegalStateException(
      "Unrecognized schedule type: %s".formatted(schedule)
    );
  }
}
