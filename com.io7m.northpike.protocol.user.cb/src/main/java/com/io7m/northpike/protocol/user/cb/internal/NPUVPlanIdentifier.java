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

import com.io7m.northpike.plans.NPPlanIdentifier;
import com.io7m.northpike.plans.NPPlanName;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1PlanIdentifier;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned64;

/**
 * A validator.
 */

public enum NPUVPlanIdentifier
  implements NPProtocolMessageValidatorType<NPPlanIdentifier, NPU1PlanIdentifier>
{
  /**
   * A validator.
   */

  PLAN_IDENTIFIER;

  @Override
  public NPU1PlanIdentifier convertToWire(
    final NPPlanIdentifier message)
  {
    return new NPU1PlanIdentifier(
      string(message.name().toString()),
      unsigned64(message.version())
    );
  }

  @Override
  public NPPlanIdentifier convertFromWire(
    final NPU1PlanIdentifier message)
  {
    return new NPPlanIdentifier(
      NPPlanName.of(message.fieldName().value()),
      message.fieldVersion().value()
    );
  }
}
