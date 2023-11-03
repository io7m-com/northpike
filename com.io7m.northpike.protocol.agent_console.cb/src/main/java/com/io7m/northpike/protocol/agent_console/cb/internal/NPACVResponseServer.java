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
import com.io7m.northpike.protocol.agent_console.NPACResponseServer;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1ResponseServer;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVAgentServerDescription.AGENT_SERVER_DESCRIPTION;

/**
 * A validator.
 */

public enum NPACVResponseServer
  implements NPProtocolMessageValidatorType<NPACResponseServer, NPAC1ResponseServer>
{
  /**
   * A validator.
   */

  RESPONSE_SERVER;

  @Override
  public NPAC1ResponseServer convertToWire(
    final NPACResponseServer message)
  {
    return new NPAC1ResponseServer(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBOptionType.fromOptional(
        message.results()
          .map(AGENT_SERVER_DESCRIPTION::convertToWire)
      )
    );
  }

  @Override
  public NPACResponseServer convertFromWire(
    final NPAC1ResponseServer message)
  {
    return new NPACResponseServer(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      message.fieldServer()
        .asOptional()
        .map(AGENT_SERVER_DESCRIPTION::convertFromWire)
    );
  }
}
