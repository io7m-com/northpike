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

import com.io7m.northpike.model.NPFormatName;
import com.io7m.northpike.model.plans.NPPlanFormatDescription;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1PlanFormat;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVPlanFormat
  implements NPProtocolMessageValidatorType<NPPlanFormatDescription, NPU1PlanFormat>
{
  /**
   * A validator.
   */

  PLAN_FORMAT;

  @Override
  public NPU1PlanFormat convertToWire(
    final NPPlanFormatDescription message)
  {
    return new NPU1PlanFormat(
      string(message.name().toString()),
      string(message.description())
    );
  }

  @Override
  public NPPlanFormatDescription convertFromWire(
    final NPU1PlanFormat message)
  {
    return new NPPlanFormatDescription(
      NPFormatName.of(message.fieldName().value()),
      message.fieldDescription().value()
    );
  }
}
