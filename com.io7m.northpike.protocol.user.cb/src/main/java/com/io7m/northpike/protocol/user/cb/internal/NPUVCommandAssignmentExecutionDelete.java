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
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBSets;
import com.io7m.northpike.model.assignments.NPAssignmentExecutionID;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentExecutionDelete;
import com.io7m.northpike.protocol.user.cb.NPU1CommandAssignmentExecutionDelete;

/**
 * A validator.
 */

public enum NPUVCommandAssignmentExecutionDelete
  implements NPProtocolMessageValidatorType<
  NPUCommandAssignmentExecutionDelete,
  NPU1CommandAssignmentExecutionDelete>
{
  /**
   * A validator.
   */

  COMMAND_ASSIGNMENT_EXECUTION_DELETE;

  @Override
  public NPU1CommandAssignmentExecutionDelete convertToWire(
    final NPUCommandAssignmentExecutionDelete message)
  {
    return new NPU1CommandAssignmentExecutionDelete(
      new CBUUID(message.messageID()),
      CBLists.ofCollection(
        message.executions(),
        x -> new CBUUID(x.value())
      )
    );
  }

  @Override
  public NPUCommandAssignmentExecutionDelete convertFromWire(
    final NPU1CommandAssignmentExecutionDelete message)
  {
    return new NPUCommandAssignmentExecutionDelete(
      message.fieldMessageId().value(),
      CBSets.toSet(
        message.fieldExecutions(),
        x -> new NPAssignmentExecutionID(x.value())
      )
    );
  }
}
