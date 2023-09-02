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

import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.model.NPToolExecutionEvaluated;
import com.io7m.northpike.protocol.agent.cb.NPA1ToolExecutionEvaluated;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVToolReference.TOOL_REFERENCE;

/**
 * A validator.
 */

public enum NPAVToolExecutionEvaluated
  implements NPProtocolMessageValidatorType<NPToolExecutionEvaluated, NPA1ToolExecutionEvaluated>
{
  /**
   * A validator.
   */

  TOOL_EXECUTION_EVALUATED;

  @Override
  public NPA1ToolExecutionEvaluated convertToWire(
    final NPToolExecutionEvaluated message)
  {
    return new NPA1ToolExecutionEvaluated(
      TOOL_REFERENCE.convertToWire(message.toolReference()),
      CBMaps.ofMapString(message.environment()),
      CBLists.ofCollectionString(message.command())
    );
  }

  @Override
  public NPToolExecutionEvaluated convertFromWire(
    final NPA1ToolExecutionEvaluated message)
  {
    return new NPToolExecutionEvaluated(
      TOOL_REFERENCE.convertFromWire(message.fieldToolReference()),
      CBMaps.toMapString(message.fieldEnvironment()),
      CBLists.toListString(message.fieldArguments())
    );
  }
}
