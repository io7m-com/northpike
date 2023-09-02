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


package com.io7m.northpike.protocol.agent.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.cb.NPA1CommandSWorkSent;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVAgentWorkItem.AGENT_WORK_ITEM;

/**
 * A validator.
 */

public enum NPAVCommandSWorkSent
  implements NPProtocolMessageValidatorType<NPACommandSWorkSent, NPA1CommandSWorkSent>
{
  /**
   * A validator.
   */

  COMMAND_WORK_SENT;

  @Override
  public NPA1CommandSWorkSent convertToWire(
    final NPACommandSWorkSent message)
  {
    return new NPA1CommandSWorkSent(
      new CBUUID(message.messageID()),
      AGENT_WORK_ITEM.convertToWire(message.workItem())
    );
  }

  @Override
  public NPACommandSWorkSent convertFromWire(
    final NPA1CommandSWorkSent message)
  {
    return new NPACommandSWorkSent(
      message.fieldMessageId().value(),
      AGENT_WORK_ITEM.convertFromWire(message.fieldWorkItem())
    );
  }
}
