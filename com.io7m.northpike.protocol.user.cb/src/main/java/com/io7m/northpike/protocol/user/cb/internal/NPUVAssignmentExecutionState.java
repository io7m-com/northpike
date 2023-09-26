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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCancelled;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreated;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateCreationFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateFailed;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRequested;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateRunning;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateSucceeded;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateType;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AssignmentExecutionState;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVAssignmentExecution.ASSIGNMENT_EXECUTION;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVAssignmentExecutionRequest.ASSIGNMENT_EXECUTION_REQUEST;

/**
 * A validator.
 */

public enum NPUVAssignmentExecutionState
  implements NPProtocolMessageValidatorType<NPAssignmentExecutionStateType, NPU1AssignmentExecutionState>
{
  /**
   * A validator.
   */

  ASSIGNMENT_EXECUTION_STATE;

  @Override
  public NPU1AssignmentExecutionState convertToWire(
    final NPAssignmentExecutionStateType message)
  {
    if (message instanceof final NPAssignmentExecutionStateCancelled c) {
      return convertToWireCancelled(c);
    }
    if (message instanceof final NPAssignmentExecutionStateCreated c) {
      return convertToWireCreated(c);
    }
    if (message instanceof final NPAssignmentExecutionStateFailed c) {
      return convertToWireFailed(c);
    }
    if (message instanceof final NPAssignmentExecutionStateRequested c) {
      return convertToWireRequested(c);
    }
    if (message instanceof final NPAssignmentExecutionStateRunning c) {
      return convertToWireRunning(c);
    }
    if (message instanceof final NPAssignmentExecutionStateSucceeded c) {
      return convertToWireSucceeded(c);
    }
    if (message instanceof final NPAssignmentExecutionStateCreationFailed c) {
      return convertToWireCreationFailed(c);
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  private static NPU1AssignmentExecutionState convertToWireCancelled(
    final NPAssignmentExecutionStateCancelled c)
  {
    return new NPU1AssignmentExecutionState.Cancelled(
      new CBUUID(c.id().value()),
      ASSIGNMENT_EXECUTION_REQUEST.convertToWire(c.request()),
      new CBOffsetDateTime(c.timeCreated()),
      new CBOffsetDateTime(c.timeStarted()),
      new CBOffsetDateTime(c.timeEnded())
    );
  }

  private static NPU1AssignmentExecutionState convertToWireCreationFailed(
    final NPAssignmentExecutionStateCreationFailed c)
  {
    return new NPU1AssignmentExecutionState.CreationFailed(
      new CBUUID(c.id().value()),
      ASSIGNMENT_EXECUTION_REQUEST.convertToWire(c.request()),
      new CBOffsetDateTime(c.timeCreated())
    );
  }

  private static NPU1AssignmentExecutionState convertToWireRequested(
    final NPAssignmentExecutionStateRequested c)
  {
    return new NPU1AssignmentExecutionState.Requested(
      new CBUUID(c.id().value()),
      ASSIGNMENT_EXECUTION_REQUEST.convertToWire(c.request()),
      new CBOffsetDateTime(c.timeCreated())
    );
  }

  private static NPU1AssignmentExecutionState convertToWireRunning(
    final NPAssignmentExecutionStateRunning c)
  {
    return new NPU1AssignmentExecutionState.Running(
      ASSIGNMENT_EXECUTION.convertToWire(c.execution()),
      new CBOffsetDateTime(c.timeCreated()),
      new CBOffsetDateTime(c.timeStarted())
    );
  }

  private static NPU1AssignmentExecutionState convertToWireSucceeded(
    final NPAssignmentExecutionStateSucceeded c)
  {
    return new NPU1AssignmentExecutionState.Succeeded(
      ASSIGNMENT_EXECUTION.convertToWire(c.execution()),
      new CBOffsetDateTime(c.timeCreated()),
      new CBOffsetDateTime(c.timeStarted()),
      new CBOffsetDateTime(c.timeEnded())
    );
  }

  private static NPU1AssignmentExecutionState convertToWireFailed(
    final NPAssignmentExecutionStateFailed c)
  {
    return new NPU1AssignmentExecutionState.Failed(
      ASSIGNMENT_EXECUTION.convertToWire(c.execution()),
      new CBOffsetDateTime(c.timeCreated()),
      new CBOffsetDateTime(c.timeStarted()),
      new CBOffsetDateTime(c.timeEnded())
    );
  }

  private static NPU1AssignmentExecutionState convertToWireCreated(
    final NPAssignmentExecutionStateCreated c)
  {
    return new NPU1AssignmentExecutionState.Created(
      new CBUUID(c.id().value()),
      new CBOffsetDateTime(c.timeCreated()),
      ASSIGNMENT_EXECUTION.convertToWire(c.execution())
    );
  }

  @Override
  public NPAssignmentExecutionStateType convertFromWire(
    final NPU1AssignmentExecutionState message)
  {
    if (message instanceof final NPU1AssignmentExecutionState.Cancelled c) {
      return convertFromWireCancelled(c);
    }
    if (message instanceof final NPU1AssignmentExecutionState.Created c) {
      return convertFromWireCreated(c);
    }
    if (message instanceof final NPU1AssignmentExecutionState.Failed c) {
      return convertFromWireFailed(c);
    }
    if (message instanceof final NPU1AssignmentExecutionState.Requested c) {
      return convertFromWireRequested(c);
    }
    if (message instanceof final NPU1AssignmentExecutionState.Running c) {
      return convertFromWireRunning(c);
    }
    if (message instanceof final NPU1AssignmentExecutionState.Succeeded c) {
      return convertFromWireSucceeded(c);
    }
    if (message instanceof final NPU1AssignmentExecutionState.CreationFailed c) {
      return convertFromWireCreationFailed(c);
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireRunning(
    final NPU1AssignmentExecutionState.Running c)
  {
    return new NPAssignmentExecutionStateRunning(
      c.fieldTimeCreated().value(),
      ASSIGNMENT_EXECUTION.convertFromWire(c.fieldExecution()),
      c.fieldTimeStarted().value()
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireFailed(
    final NPU1AssignmentExecutionState.Failed c)
  {
    return new NPAssignmentExecutionStateFailed(
      c.fieldTimeCreated().value(),
      ASSIGNMENT_EXECUTION.convertFromWire(c.fieldExecution()),
      c.fieldTimeStarted().value(),
      c.fieldTimeEnded().value()
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireSucceeded(
    final NPU1AssignmentExecutionState.Succeeded c)
  {
    return new NPAssignmentExecutionStateSucceeded(
      c.fieldTimeCreated().value(),
      ASSIGNMENT_EXECUTION.convertFromWire(c.fieldExecution()),
      c.fieldTimeStarted().value(),
      c.fieldTimeEnded().value()
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireCreationFailed(
    final NPU1AssignmentExecutionState.CreationFailed c)
  {
    return new NPAssignmentExecutionStateCreationFailed(
      new NPAssignmentExecutionID(c.fieldId().value()),
      ASSIGNMENT_EXECUTION_REQUEST.convertFromWire(c.fieldRequest()),
      c.fieldTimeCreated().value()
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireRequested(
    final NPU1AssignmentExecutionState.Requested c)
  {
    return new NPAssignmentExecutionStateRequested(
      new NPAssignmentExecutionID(c.fieldId().value()),
      ASSIGNMENT_EXECUTION_REQUEST.convertFromWire(c.fieldRequest()),
      c.fieldTimeCreated().value()
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireCreated(
    final NPU1AssignmentExecutionState.Created c)
  {
    return new NPAssignmentExecutionStateCreated(
      c.fieldTimeCreated().value(),
      ASSIGNMENT_EXECUTION.convertFromWire(c.fieldExecution())
    );
  }

  private static NPAssignmentExecutionStateType convertFromWireCancelled(
    final NPU1AssignmentExecutionState.Cancelled c)
  {
    return new NPAssignmentExecutionStateCancelled(
      new NPAssignmentExecutionID(c.fieldId().value()),
      ASSIGNMENT_EXECUTION_REQUEST.convertFromWire(c.fieldRequest()),
      c.fieldTimeCreated().value(),
      c.fieldTimeStarted().value(),
      c.fieldTimeEnded().value()
    );
  }
}
