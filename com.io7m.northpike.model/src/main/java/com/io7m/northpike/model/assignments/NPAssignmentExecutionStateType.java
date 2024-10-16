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


package com.io7m.northpike.model.assignments;

import java.time.OffsetDateTime;
import java.util.Map;

/**
 * The status of an assignment execution.
 */

public sealed interface NPAssignmentExecutionStateType
  permits NPAssignmentExecutionStateCancelled,
  NPAssignmentExecutionStateCreatedType,
  NPAssignmentExecutionStateCreationFailed,
  NPAssignmentExecutionStateRequested
{
  /**
   * @return The execution ID
   */

  NPAssignmentExecutionID id();

  /**
   * @return The request that started the execution
   */

  NPAssignmentExecutionRequest request();

  /**
   * @return The time the execution was created
   */

  OffsetDateTime timeCreated();

  /**
   * @return The execution status as a set of attributes for telemetry/logging
   */

  Map<String, String> asAttributes();

  /**
   * @return The state kind as a scalar enumeration
   */

  NPAssignmentExecutionStateKind state();

  /**
   * @return The name of this status value
   */

  default String stateName()
  {
    return this.state().name();
  }
}
