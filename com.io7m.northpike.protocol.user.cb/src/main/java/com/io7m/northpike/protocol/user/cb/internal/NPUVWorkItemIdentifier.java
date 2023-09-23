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
import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPWorkItemIdentifier;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1WorkItemIdentifier;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVWorkItemIdentifier
  implements NPProtocolMessageValidatorType<NPWorkItemIdentifier, NPU1WorkItemIdentifier>
{
  /**
   * A validator.
   */

  WORK_ITEM_IDENTIFIER;

  @Override
  public NPU1WorkItemIdentifier convertToWire(
    final NPWorkItemIdentifier message)
  {
    return new NPU1WorkItemIdentifier(
      new CBUUID(message.assignmentExecutionId()),
      string(message.planElementName().value())
    );
  }

  @Override
  public NPWorkItemIdentifier convertFromWire(
    final NPU1WorkItemIdentifier message)
  {
    return new NPWorkItemIdentifier(
      message.fieldExecution().value(),
      new RDottedName(message.fieldPlanElement().value())
    );
  }
}
