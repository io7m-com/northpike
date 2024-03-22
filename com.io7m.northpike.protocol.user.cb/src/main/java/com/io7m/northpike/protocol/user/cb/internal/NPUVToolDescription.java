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
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.model.NPToolDescription;
import com.io7m.northpike.model.NPToolExecutionName;
import com.io7m.northpike.model.NPToolName;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1Tool;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVVersionRange.VERSION_RANGE;

/**
 * A validator.
 */

public enum NPUVToolDescription
  implements NPProtocolMessageValidatorType<NPToolDescription, NPU1Tool>
{
  /**
   * A validator.
   */

  TOOL_DESCRIPTION;

  @Override
  public NPU1Tool convertToWire(
    final NPToolDescription message)
  {
    return new NPU1Tool(
      string(message.name().toString()),
      string(message.description()),
      VERSION_RANGE.convertToWire(message.versions()),
      CBMaps.ofMap(
        message.defaultExecutions(),
        k -> string(k.toString()),
        CBLists::ofCollectionString
      )
    );
  }

  @Override
  public NPToolDescription convertFromWire(
    final NPU1Tool message)
  {
    return new NPToolDescription(
      NPToolName.of(message.fieldName().value()),
      message.fieldDescription().value(),
      VERSION_RANGE.convertFromWire(message.fieldVersions()),
      CBMaps.toMap(
        message.fieldExecutions(),
        k -> NPToolExecutionName.of(k.value()),
        v -> CBLists.toList(v, CBString::value)
      )
    );
  }
}
