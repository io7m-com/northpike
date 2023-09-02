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
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemStarted;
import com.io7m.northpike.protocol.agent.cb.NPA1CommandCWorkItemStarted;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVWorkItemIdentifier.WORK_ITEM_IDENTIFIER;

/**
 * A validator.
 */

public enum NPAVCommandCWorkItemStarted
  implements NPProtocolMessageValidatorType<NPACommandCWorkItemStarted, NPA1CommandCWorkItemStarted>
{
  /**
   * A validator.
   */

  COMMAND_WORK_ITEM_STARTED;

  @Override
  public NPA1CommandCWorkItemStarted convertToWire(
    final NPACommandCWorkItemStarted message)
  {
    return new NPA1CommandCWorkItemStarted(
      new CBUUID(message.messageID()),
      WORK_ITEM_IDENTIFIER.convertToWire(message.identifier())
    );
  }

  @Override
  public NPACommandCWorkItemStarted convertFromWire(
    final NPA1CommandCWorkItemStarted message)
  {
    return new NPACommandCWorkItemStarted(
      message.fieldMessageId().value(),
      WORK_ITEM_IDENTIFIER.convertFromWire(message.fieldWorkItem())
    );
  }
}
