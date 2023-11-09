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


package com.io7m.northpike.protocol.agent_console.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerList;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1CommandServerList;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;

/**
 * A validator.
 */

public enum NPACVCommandServerList
  implements NPProtocolMessageValidatorType<NPACCommandServerList, NPAC1CommandServerList>
{
  /**
   * A validator.
   */

  COMMAND_SERVER_LIST;

  @Override
  public NPAC1CommandServerList convertToWire(
    final NPACCommandServerList message)
  {
    return new NPAC1CommandServerList(
      new CBUUID(message.messageID()),
      CBOptionType.fromOptional(
        message.offset()
          .map(x -> new CBUUID(x.value()))
      ),
      unsigned32(message.limit())
    );
  }

  @Override
  public NPACCommandServerList convertFromWire(
    final NPAC1CommandServerList message)
  {
    return new NPACCommandServerList(
      message.fieldMessageId().value(),
      message.fieldOffset()
        .asOptional()
        .map(x -> new NPAgentServerID(x.value())),
      message.fieldLimit().value()
    );
  }
}
