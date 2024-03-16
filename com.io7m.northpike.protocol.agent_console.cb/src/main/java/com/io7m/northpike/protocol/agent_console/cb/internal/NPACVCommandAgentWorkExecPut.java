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
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentWorkExecPut;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1CommandAgentWorkExecPut;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVWorkExecutor.WORK_EXECUTOR;

/**
 * A validator.
 */

public enum NPACVCommandAgentWorkExecPut
  implements NPProtocolMessageValidatorType<NPACCommandAgentWorkExecPut, NPAC1CommandAgentWorkExecPut>
{
  /**
   * A validator.
   */

  COMMAND_AGENT_WORK_EXEC_PUT;

  @Override
  public NPAC1CommandAgentWorkExecPut convertToWire(
    final NPACCommandAgentWorkExecPut message)
  {
    return new NPAC1CommandAgentWorkExecPut(
      new CBUUID(message.messageID()),
      string(message.name().toString()),
      CBOptionType.fromOptional(
        message.workExecutor()
          .map(WORK_EXECUTOR::convertToWire)
      )
    );
  }

  @Override
  public NPACCommandAgentWorkExecPut convertFromWire(
    final NPAC1CommandAgentWorkExecPut message)
  {
    return new NPACCommandAgentWorkExecPut(
      message.fieldMessageId().value(),
      NPAgentLocalName.of(message.fieldAgent().value()),
      message.fieldWorkExecutor()
        .asOptional()
        .map(WORK_EXECUTOR::convertFromWire)
    );
  }
}
