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


package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleHourlyHashed;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleNone;
import com.io7m.northpike.model.assignments.NPAssignmentScheduleType;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AssignmentSchedule;

/**
 * A validator.
 */

public enum NPUVAssignmentSchedule
  implements NPProtocolMessageValidatorType<NPAssignmentScheduleType, NPU1AssignmentSchedule>
{
  /**
   * A validator.
   */

  ASSIGNMENT_SCHEDULE;

  @Override
  public NPU1AssignmentSchedule convertToWire(
    final NPAssignmentScheduleType message)
  {
    if (message instanceof NPAssignmentScheduleNone) {
      return new NPU1AssignmentSchedule.None();
    }

    if (message instanceof final NPAssignmentScheduleHourlyHashed hashed) {
      return new NPU1AssignmentSchedule.HourlyHashed(
        new CBOffsetDateTime(hashed.commitAgeCutoff())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPAssignmentScheduleType convertFromWire(
    final NPU1AssignmentSchedule message)
  {
    if (message instanceof NPU1AssignmentSchedule.None) {
      return NPAssignmentScheduleNone.SCHEDULE_NONE;
    }

    if (message instanceof final NPU1AssignmentSchedule.HourlyHashed c) {
      return new NPAssignmentScheduleHourlyHashed(c.fieldAgeCutoff().value());
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
