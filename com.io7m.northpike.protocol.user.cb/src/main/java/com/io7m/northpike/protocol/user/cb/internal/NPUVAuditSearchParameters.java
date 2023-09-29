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

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.northpike.model.NPAuditSearchParameters;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AuditSearchParameters;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVStrings.STRINGS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVTimeRange.TIME_RANGE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVUserOrAgent.USER_OR_AGENT;

/**
 * A validator.
 */

public enum NPUVAuditSearchParameters
  implements NPProtocolMessageValidatorType<NPAuditSearchParameters, NPU1AuditSearchParameters>
{
  /**
   * A validator.
   */

  AUDIT_SEARCH_PARAMETERS;

  private static final NPUVComparisonsExact<String, CBString> EXACT_VALIDATOR =
    new NPUVComparisonsExact<>(STRINGS);

  @Override
  public NPU1AuditSearchParameters convertToWire(
    final NPAuditSearchParameters message)
    throws NPProtocolException
  {
    return new NPU1AuditSearchParameters(
      CBOptionType.fromOptional(message.owner().map(USER_OR_AGENT::convertToWire)),
      EXACT_VALIDATOR.convertToWire(message.type()),
      TIME_RANGE.convertToWire(message.timeRange()),
      unsigned32(message.pageSize())
    );
  }

  @Override
  public NPAuditSearchParameters convertFromWire(
    final NPU1AuditSearchParameters message)
    throws NPProtocolException
  {
    return new NPAuditSearchParameters(
      message.fieldOwner().asOptional().map(USER_OR_AGENT::convertFromWire),
      EXACT_VALIDATOR.convertFromWire(message.fieldType()),
      TIME_RANGE.convertFromWire(message.fieldTimeRange()),
      message.fieldPageSize().value()
    );
  }
}
