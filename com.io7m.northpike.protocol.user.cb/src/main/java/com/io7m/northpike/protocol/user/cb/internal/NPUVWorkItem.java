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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.model.NPWorkItem;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1WorkItem;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVWorkItemIdentifier.WORK_ITEM_IDENTIFIER;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVWorkItemStatus.WORK_ITEM_STATUS;

/**
 * A validator.
 */

public enum NPUVWorkItem
  implements NPProtocolMessageValidatorType<NPWorkItem, NPU1WorkItem>
{
  /**
   * A validator.
   */

  WORK_ITEM;

  @Override
  public NPU1WorkItem convertToWire(
    final NPWorkItem message)
  {
    return new NPU1WorkItem(
      WORK_ITEM_IDENTIFIER.convertToWire(message.identifier()),
      CBOptionType.fromOptional(
        message.selectedAgent()
          .map(NPAgentID::value)
          .map(CBUUID::new)
      ),
      WORK_ITEM_STATUS.convertToWire(message.status())
    );
  }

  @Override
  public NPWorkItem convertFromWire(
    final NPU1WorkItem message)
  {
    return new NPWorkItem(
      WORK_ITEM_IDENTIFIER.convertFromWire(message.fieldIdentifier()),
      message.fieldSelectedAgent()
        .asOptional()
        .map(CBUUID::value)
        .map(NPAgentID::new),
      WORK_ITEM_STATUS.convertFromWire(message.fieldStatus())
    );
  }
}
