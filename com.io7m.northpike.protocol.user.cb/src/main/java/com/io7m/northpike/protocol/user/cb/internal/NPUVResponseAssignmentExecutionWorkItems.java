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
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUResponseAssignmentExecutionWorkItems;
import com.io7m.northpike.protocol.user.cb.NPU1ResponseAssignmentExecutionWorkItems;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVWorkItem.WORK_ITEM;

/**
 * A validator.
 */

public enum NPUVResponseAssignmentExecutionWorkItems
  implements NPProtocolMessageValidatorType<
  NPUResponseAssignmentExecutionWorkItems,
  NPU1ResponseAssignmentExecutionWorkItems>
{
  /**
   * A validator.
   */

  RESPONSE_ASSIGNMENT_EXECUTION_WORK_ITEMS;

  @Override
  public NPU1ResponseAssignmentExecutionWorkItems convertToWire(
    final NPUResponseAssignmentExecutionWorkItems message)
  {
    return new NPU1ResponseAssignmentExecutionWorkItems(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBLists.ofCollection(
        message.results(),
        WORK_ITEM::convertToWire
      )
    );
  }

  @Override
  public NPUResponseAssignmentExecutionWorkItems convertFromWire(
    final NPU1ResponseAssignmentExecutionWorkItems message)
  {
    return new NPUResponseAssignmentExecutionWorkItems(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      CBSets.toSet(
        message.fieldResults(),
        WORK_ITEM::convertFromWire
      )
    );
  }
}
