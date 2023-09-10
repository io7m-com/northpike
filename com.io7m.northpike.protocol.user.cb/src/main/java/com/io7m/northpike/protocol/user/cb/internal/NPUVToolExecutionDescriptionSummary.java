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

import com.io7m.northpike.model.NPToolExecutionDescriptionSummary;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1ToolExecutionDescriptionSummary;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVToolExecutionIdentifier.TOOL_EXECUTION_IDENTIFIER;

/**
 * A validator.
 */

public enum NPUVToolExecutionDescriptionSummary
  implements NPProtocolMessageValidatorType<
  NPToolExecutionDescriptionSummary,
  NPU1ToolExecutionDescriptionSummary>
{
  /**
   * A validator.
   */

  TOOL_EXECUTION_DESCRIPTION_SUMMARY;

  @Override
  public NPU1ToolExecutionDescriptionSummary convertToWire(
    final NPToolExecutionDescriptionSummary message)
  {
    return new NPU1ToolExecutionDescriptionSummary(
      TOOL_EXECUTION_IDENTIFIER.convertToWire(message.identifier()),
      string(message.tool().toString()),
      string(message.description())
    );
  }

  @Override
  public NPToolExecutionDescriptionSummary convertFromWire(
    final NPU1ToolExecutionDescriptionSummary message)
  {
    return new NPToolExecutionDescriptionSummary(
      TOOL_EXECUTION_IDENTIFIER.convertFromWire(message.fieldIdentifier()),
      NPToolName.of(message.fieldToolName().value()),
      message.fieldDescription().value()
    );
  }
}
