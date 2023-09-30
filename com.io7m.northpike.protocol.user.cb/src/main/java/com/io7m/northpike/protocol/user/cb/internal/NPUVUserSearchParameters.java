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
import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.model.NPUserSearchParameters;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1UserSearchParameters;

import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVStrings.STRINGS;

/**
 * A validator.
 */

public enum NPUVUserSearchParameters
  implements NPProtocolMessageValidatorType<NPUserSearchParameters, NPU1UserSearchParameters>
{
  /**
   * A validator.
   */

  USER_SEARCH_PARAMETERS;

  private static final NPUVComparisonsFuzzy<String, CBString> FUZZY_VALIDATOR =
    new NPUVComparisonsFuzzy<>(STRINGS);
  private static final NPUVComparisonsSet<String, CBString> SET_VALIDATOR =
    new NPUVComparisonsSet<>(STRINGS);

  @Override
  public NPU1UserSearchParameters convertToWire(
    final NPUserSearchParameters message)
    throws NPProtocolException
  {
    return new NPU1UserSearchParameters(
      unsigned32(message.pageSize()),
      FUZZY_VALIDATOR.convertToWire(message.name()),
      SET_VALIDATOR.convertToWire(message.roles().map(x -> x.value().value()))
    );
  }

  @Override
  public NPUserSearchParameters convertFromWire(
    final NPU1UserSearchParameters message)
    throws NPProtocolException
  {
    return new NPUserSearchParameters(
      FUZZY_VALIDATOR.convertFromWire(message.fieldName()),
      SET_VALIDATOR.convertFromWire(message.fieldRoles()).map(MRoleName::of),
      message.fieldPageSize().value()
    );
  }
}
