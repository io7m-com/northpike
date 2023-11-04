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
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentServerAssign;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1CommandAgentServerAssign;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVCommandAgentServerAssign
  implements NPProtocolMessageValidatorType<NPACCommandAgentServerAssign, NPAC1CommandAgentServerAssign>
{
  /**
   * A validator.
   */

  COMMAND_AGENT_SERVER_ASSIGN;

  @Override
  public NPAC1CommandAgentServerAssign convertToWire(
    final NPACCommandAgentServerAssign message)
  {
    return new NPAC1CommandAgentServerAssign(
      new CBUUID(message.messageID()),
      string(message.name().toString()),
      CBOptionType.fromOptional(
        message.server()
          .map(x -> new CBUUID(x.value()))
      )
    );
  }

  @Override
  public NPACCommandAgentServerAssign convertFromWire(
    final NPAC1CommandAgentServerAssign message)
  {
    return new NPACCommandAgentServerAssign(
      message.fieldMessageId().value(),
      NPAgentLocalName.of(message.fieldAgentName().value()),
      message.fieldServer()
        .asOptional()
        .map(x -> new NPAgentServerID(x.value()))
    );
  }
}
