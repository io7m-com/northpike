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
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1AgentDescription;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVAgentPublicKey.AGENT_PUBLIC_KEY;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVWorkExecutor.WORK_EXECUTOR;

/**
 * A validator.
 */

public enum NPACVAgentDescription
  implements NPProtocolMessageValidatorType<NPACResponseAgent.Result, NPAC1AgentDescription>
{
  /**
   * A validator.
   */

  AGENT_DESCRIPTION;

  @Override
  public NPAC1AgentDescription convertToWire(
    final NPACResponseAgent.Result message)
  {
    return new NPAC1AgentDescription(
      string(message.name().toString()),
      AGENT_PUBLIC_KEY.convertToWire(message.publicKey()),
      CBOptionType.fromOptional(
        message.server()
          .map(x -> new CBUUID(x.value()))
      ),
      CBOptionType.fromOptional(
        message.workExecutor()
          .map(WORK_EXECUTOR::convertToWire)
      )
    );
  }

  @Override
  public NPACResponseAgent.Result convertFromWire(
    final NPAC1AgentDescription message)
    throws NPProtocolException
  {
    return new NPACResponseAgent.Result(
      NPAgentLocalName.of(message.fieldName().value()),
      AGENT_PUBLIC_KEY.convertFromWire(message.fieldPublicKey()),
      message.fieldServer()
        .asOptional()
        .map(x -> new NPAgentServerID(x.value())),
      message.fieldWorkExec()
        .asOptional()
        .map(WORK_EXECUTOR::convertFromWire)
    );
  }
}
