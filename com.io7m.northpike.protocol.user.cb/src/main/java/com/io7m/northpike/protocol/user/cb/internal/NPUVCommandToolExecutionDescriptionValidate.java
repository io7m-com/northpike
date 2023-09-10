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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.cb.NPU1CommandToolExecutionDescriptionValidate;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVToolExecutionDescription.TOOL_EXECUTION_DESCRIPTION;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVToolExecutionVariable.TOOL_EXECUTION_VARIABLE;

/**
 * A validator.
 */

public enum NPUVCommandToolExecutionDescriptionValidate
  implements NPProtocolMessageValidatorType<
  NPUCommandToolExecutionDescriptionValidate,
  NPU1CommandToolExecutionDescriptionValidate>
{
  /**
   * A validator.
   */

  COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE;

  @Override
  public NPU1CommandToolExecutionDescriptionValidate convertToWire(
    final NPUCommandToolExecutionDescriptionValidate message)
  {
    return new NPU1CommandToolExecutionDescriptionValidate(
      new CBUUID(message.messageID()),
      CBLists.ofCollection(
        message.variables(),
        TOOL_EXECUTION_VARIABLE::convertToWire
      ),
      TOOL_EXECUTION_DESCRIPTION.convertToWire(message.description())
    );
  }

  @Override
  public NPUCommandToolExecutionDescriptionValidate convertFromWire(
    final NPU1CommandToolExecutionDescriptionValidate message)
  {
    return new NPUCommandToolExecutionDescriptionValidate(
      message.fieldMessageId().value(),
      CBLists.toList(
        message.fieldVariables(),
        TOOL_EXECUTION_VARIABLE::convertFromWire
      ),
      TOOL_EXECUTION_DESCRIPTION.convertFromWire(message.fieldDescription())
    );
  }
}
