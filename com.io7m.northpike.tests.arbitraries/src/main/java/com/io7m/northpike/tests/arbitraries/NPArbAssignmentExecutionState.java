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


package com.io7m.northpike.tests.arbitraries;

import com.io7m.northpike.model.assignments.NPAssignmentExecution;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionRequest;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCancelled;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.Combinators;

import java.time.OffsetDateTime;

public final class NPArbAssignmentExecutionState
  extends NPArbAbstract<NPAssignmentExecutionStateType>
{
  public NPArbAssignmentExecutionState()
  {
    super(
      NPAssignmentExecutionStateType.class,
      () -> {
        return Arbitraries.oneOf(
          cancelled(),
          created(),
          creationFailed(),
          failed(),
          requested(),
          running(),
          succeeded()
        );
      }
    );
  }

  private static Arbitrary<NPAssignmentExecutionStateType> succeeded()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(NPAssignmentExecution.class),
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(OffsetDateTime.class)
    ).as(NPAssignmentExecutionStateSucceeded::new);
  }

  private static Arbitrary<NPAssignmentExecutionStateType> running()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(NPAssignmentExecution.class),
      Arbitraries.defaultFor(OffsetDateTime.class)
    ).as(NPAssignmentExecutionStateRunning::new);
  }

  private static Arbitrary<NPAssignmentExecutionStateType> requested()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(NPAssignmentExecutionID.class),
      Arbitraries.defaultFor(NPAssignmentExecutionRequest.class),
      Arbitraries.defaultFor(OffsetDateTime.class)
    ).as(NPAssignmentExecutionStateRequested::new);
  }

  private static Arbitrary<NPAssignmentExecutionStateType> failed()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(NPAssignmentExecution.class),
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(OffsetDateTime.class)
    ).as(NPAssignmentExecutionStateFailed::new);
  }

  private static Arbitrary<NPAssignmentExecutionStateType> creationFailed()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(NPAssignmentExecutionID.class),
      Arbitraries.defaultFor(NPAssignmentExecutionRequest.class),
      Arbitraries.defaultFor(OffsetDateTime.class)
    ).as(NPAssignmentExecutionStateCreationFailed::new);
  }

  private static Arbitrary<NPAssignmentExecutionStateType> created()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(NPAssignmentExecution.class)
    ).as(NPAssignmentExecutionStateCreated::new);
  }

  private static Arbitrary<NPAssignmentExecutionStateType> cancelled()
  {
    return Combinators.combine(
      Arbitraries.defaultFor(NPAssignmentExecutionID.class),
      Arbitraries.defaultFor(NPAssignmentExecutionRequest.class),
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(OffsetDateTime.class),
      Arbitraries.defaultFor(OffsetDateTime.class)
    ).as(NPAssignmentExecutionStateCancelled::new);
  }
}
