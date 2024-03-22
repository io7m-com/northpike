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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.cedarbridge.runtime.time.CBOffsetDateTime;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemOutput;
import com.io7m.northpike.protocol.agent.cb.NPA1CommandCWorkItemOutput;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned64;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVException.EXCEPTION;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVWorkItemIdentifier.WORK_ITEM_IDENTIFIER;

/**
 * A validator.
 */

public enum NPAVCommandCWorkItemOutput
  implements NPProtocolMessageValidatorType<NPACommandCWorkItemOutput, NPA1CommandCWorkItemOutput>
{
  /**
   * A validator.
   */

  COMMAND_WORK_ITEM_OUTPUT;

  @Override
  public NPA1CommandCWorkItemOutput convertToWire(
    final NPACommandCWorkItemOutput message)
  {
    return new NPA1CommandCWorkItemOutput(
      new CBUUID(message.messageID()),
      new CBOffsetDateTime(message.timestamp()),
      unsigned64(message.eventIndex()),
      string(message.eventType()),
      WORK_ITEM_IDENTIFIER.convertToWire(message.identifier()),
      CBMaps.ofMapString(message.attributes()),
      string(message.message()),
      CBOptionType.fromOptional(
        message.exception()
          .map(EXCEPTION::convertToWire)
      )
    );
  }

  @Override
  public NPACommandCWorkItemOutput convertFromWire(
    final NPA1CommandCWorkItemOutput message)
  {
    return new NPACommandCWorkItemOutput(
      message.fieldMessageId().value(),
      message.fieldTimestamp().value(),
      message.fieldIndex().value(),
      message.fieldType().value(),
      WORK_ITEM_IDENTIFIER.convertFromWire(message.fieldWorkItem()),
      CBMaps.toMapString(message.fieldAttributes()),
      message.fieldOutput().value(),
      message.fieldException()
        .asOptional()
        .map(EXCEPTION::convertFromWire)
    );
  }
}
