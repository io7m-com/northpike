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

import com.io7m.cedarbridge.runtime.api.CBCore;
import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1StructuredError;
import com.io7m.seltzer.api.SStructuredError;

import java.util.Optional;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVSStructuredError
  implements NPProtocolMessageValidatorType<SStructuredError<String>, NPU1StructuredError>
{
  /**
   * A validator.
   */

  STRUCTURED_ERROR;

  @Override
  public NPU1StructuredError convertToWire(
    final SStructuredError<String> message)
  {
    return new NPU1StructuredError(
      string(message.errorCode()),
      string(message.message()),
      CBMaps.ofMapString(message.attributes()),
      CBOptionType.fromOptional(message.remediatingAction().map(CBCore::string))
    );
  }

  @Override
  public SStructuredError<String> convertFromWire(
    final NPU1StructuredError message)
  {
    return new SStructuredError<>(
      message.fieldErrorCode().value(),
      message.fieldMessage().value(),
      CBMaps.toMapString(message.fieldAttributes()),
      message.fieldRemediatingAction()
        .asOptional().map(CBString::value),
      Optional.empty()
    );
  }
}
