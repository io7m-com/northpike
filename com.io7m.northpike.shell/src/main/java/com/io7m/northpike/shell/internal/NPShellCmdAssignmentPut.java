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

package com.io7m.northpike.shell.internal;

import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.assignments.NPAssignment;
import com.io7m.northpike.model.assignments.NPAssignmentName;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleKind;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleType;
import com.io7m.northpike.model.plans.NPPlanIdentifier;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.repetoir.core.RPServiceDirectoryType;

import java.time.OffsetDateTime;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

/**
 * "assignment-put"
 */

public final class NPShellCmdAssignmentPut
  extends NPShellCmdAbstractCR<NPUCommandAssignmentPut, NPUResponseOK>
{
  private static final QParameterNamed1<NPAssignmentName> NAME =
    new QParameterNamed1<>(
      "--name",
      List.of(),
      new QConstant("The assignment name."),
      Optional.empty(),
      NPAssignmentName.class
    );

  private static final QParameterNamed1<NPPlanIdentifier> PLAN =
    new QParameterNamed1<>(
      "--plan",
      List.of(),
      new QConstant("The plan identifier."),
      Optional.empty(),
      NPPlanIdentifier.class
    );

  private static final QParameterNamed1<NPRepositoryID> REPOSITORY =
    new QParameterNamed1<>(
      "--repository",
      List.of(),
      new QConstant("The repository ID."),
      Optional.empty(),
      NPRepositoryID.class
    );

  private static final QParameterNamed1<NPAssignmentScheduleKind> SCHEDULE =
    new QParameterNamed1<>(
      "--schedule",
      List.of(),
      new QConstant("The schedule kind."),
      Optional.of(NPAssignmentScheduleKind.NONE),
      NPAssignmentScheduleKind.class
    );

  private static final QParameterNamed1<OffsetDateTime> SCHEDULE_COMMIT_AGE_CUTOFF =
    new QParameterNamed1<>(
      "--schedule-commit-age-cutoff",
      List.of(),
      new QConstant("The schedule commit age cutoff."),
      Optional.of(
        OffsetDateTime.now()
          .withHour(0)
          .withMinute(0)
          .withSecond(0)
          .withNano(0)
        ),
      OffsetDateTime.class
    );

  /**
   * Construct a command.
   *
   * @param inServices The service directory
   */

  public NPShellCmdAssignmentPut(
    final RPServiceDirectoryType inServices)
  {
    super(
      inServices,
      new QCommandMetadata(
        "assignment-put",
        new QConstant("Create/update an assignment."),
        Optional.empty()
      ),
      NPUCommandAssignmentPut.class,
      NPUResponseOK.class
    );
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return List.of(
      NAME,
      PLAN,
      REPOSITORY,
      SCHEDULE,
      SCHEDULE_COMMIT_AGE_CUTOFF
    );
  }

  @Override
  protected NPUCommandAssignmentPut onCreateCommand(
    final QCommandContextType context)
  {
    return new NPUCommandAssignmentPut(
      UUID.randomUUID(),
      new NPAssignment(
        context.parameterValue(NAME),
        context.parameterValue(REPOSITORY),
        context.parameterValue(PLAN),
        schedule(context)
      )
    );
  }

  private static NPAssignmentScheduleType schedule(
    final QCommandContextType context)
  {
    return switch (context.parameterValue(SCHEDULE)) {
      case NONE -> {
        yield NPAssignmentScheduleNone.SCHEDULE_NONE;
      }
      case HOURLY_HASHED -> {
        yield new NPAssignmentScheduleHourlyHashed(
          context.parameterValue(SCHEDULE_COMMIT_AGE_CUTOFF)
        );
      }
    };
  }

  @Override
  protected void onFormatResponse(
    final QCommandContextType context,
    final NPUResponseOK response)
    throws Exception
  {

  }
}
