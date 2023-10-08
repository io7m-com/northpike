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

import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.northpike.model.NPToolExecutionDescriptionSearchParameters;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1ToolExecutionDescriptionSearchParameters;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVToolName.TOOL_NAME;

/**
 * A validator.
 */

public enum NPUVToolExecutionDescriptionSearchParameters
  implements NPProtocolMessageValidatorType<
  NPToolExecutionDescriptionSearchParameters,
  NPU1ToolExecutionDescriptionSearchParameters>
{
  /**
   * A validator.
   */

  TOOL_EXECUTION_DESCRIPTION_SEARCH_PARAMETERS;

  private static final NPUVComparisonsExact<NPToolName, CBString> TOOL_NAME_VALIDATOR =
    new NPUVComparisonsExact<>(TOOL_NAME);

  @Override
  public NPU1ToolExecutionDescriptionSearchParameters convertToWire(
    final NPToolExecutionDescriptionSearchParameters message)
    throws NPProtocolException
  {
    return new NPU1ToolExecutionDescriptionSearchParameters(
      TOOL_NAME_VALIDATOR.convertToWire(message.forTool()),
      unsigned32(message.pageSize())
    );
  }

  @Override
  public NPToolExecutionDescriptionSearchParameters convertFromWire(
    final NPU1ToolExecutionDescriptionSearchParameters message)
    throws NPProtocolException
  {
    return new NPToolExecutionDescriptionSearchParameters(
      TOOL_NAME_VALIDATOR.convertFromWire(message.fieldToolName()),
      message.fieldPageSize().value()
    );
  }
}
