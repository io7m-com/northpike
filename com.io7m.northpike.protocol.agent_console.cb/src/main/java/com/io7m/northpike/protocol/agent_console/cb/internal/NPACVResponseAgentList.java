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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgentList;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1ResponseAgentList;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVResponseAgentList
  implements NPProtocolMessageValidatorType<NPACResponseAgentList, NPAC1ResponseAgentList>
{
  /**
   * A validator.
   */

  RESPONSE_AGENT_LIST;

  @Override
  public NPAC1ResponseAgentList convertToWire(
    final NPACResponseAgentList message)
  {
    return new NPAC1ResponseAgentList(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBLists.ofCollection(
        message.results(),
        x -> string(x.toString())
      )
    );
  }

  @Override
  public NPACResponseAgentList convertFromWire(
    final NPAC1ResponseAgentList message)
  {
    return new NPACResponseAgentList(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      CBLists.toList(
        message.fieldResults(),
        x -> NPAgentLocalName.of(x.value())
      )
    );
  }
}
