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

import com.io7m.northpike.model.assignments.NPAssignmentExecutionStateKind;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AssignmentExecutionStateKind;

/**
 * A validator.
 */

public enum NPUVAssignmentExecutionStateKind
  implements NPProtocolMessageValidatorType<
  NPAssignmentExecutionStateKind, NPU1AssignmentExecutionStateKind>
{
  /**
   * A validator.
   */

  ASSIGNMENT_EXECUTION_STATE_KIND;

  @Override
  public NPU1AssignmentExecutionStateKind convertToWire(
    final NPAssignmentExecutionStateKind message)
  {
    return switch (message) {
      case CANCELLED -> new NPU1AssignmentExecutionStateKind.Cancelled();
      case CREATED -> new NPU1AssignmentExecutionStateKind.Created();
      case CREATION_FAILED ->
        new NPU1AssignmentExecutionStateKind.CreationFailed();
      case FAILED -> new NPU1AssignmentExecutionStateKind.Failed();
      case REQUESTED -> new NPU1AssignmentExecutionStateKind.Requested();
      case RUNNING -> new NPU1AssignmentExecutionStateKind.Running();
      case SUCCEEDED -> new NPU1AssignmentExecutionStateKind.Succeeded();
    };
  }

  @Override
  public NPAssignmentExecutionStateKind convertFromWire(
    final NPU1AssignmentExecutionStateKind message)
  {
    if (message instanceof final NPU1AssignmentExecutionStateKind.Cancelled c) {
      return NPAssignmentExecutionStateKind.CANCELLED;
    }
    if (message instanceof final NPU1AssignmentExecutionStateKind.Created c) {
      return NPAssignmentExecutionStateKind.CREATED;
    }
    if (message instanceof final NPU1AssignmentExecutionStateKind.Failed c) {
      return NPAssignmentExecutionStateKind.FAILED;
    }
    if (message instanceof final NPU1AssignmentExecutionStateKind.Requested c) {
      return NPAssignmentExecutionStateKind.REQUESTED;
    }
    if (message instanceof final NPU1AssignmentExecutionStateKind.Running c) {
      return NPAssignmentExecutionStateKind.RUNNING;
    }
    if (message instanceof final NPU1AssignmentExecutionStateKind.Succeeded c) {
      return NPAssignmentExecutionStateKind.SUCCEEDED;
    }
    if (message instanceof final NPU1AssignmentExecutionStateKind.CreationFailed c) {
      return NPAssignmentExecutionStateKind.CREATION_FAILED;
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
