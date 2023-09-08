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
import com.io7m.cedarbridge.runtime.convenience.CBSets;
import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUResponseRolesGet;
import com.io7m.northpike.protocol.user.cb.NPU1ResponseRolesGet;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVResponseRolesGet
  implements NPProtocolMessageValidatorType<NPUResponseRolesGet, NPU1ResponseRolesGet>
{
  /**
   * A validator.
   */

  RESPONSE_ROLES_GET;

  @Override
  public NPU1ResponseRolesGet convertToWire(
    final NPUResponseRolesGet message)
  {
    return new NPU1ResponseRolesGet(
      new CBUUID(message.messageID()),
      new CBUUID(message.correlationID()),
      CBLists.ofCollection(message.roles(), x -> string(x.value().value()))
    );
  }

  @Override
  public NPUResponseRolesGet convertFromWire(
    final NPU1ResponseRolesGet message)
  {
    return new NPUResponseRolesGet(
      message.fieldMessageId().value(),
      message.fieldCorrelationId().value(),
      CBSets.toSet(message.fieldRoles(), x -> MRoleName.of(x.value()))
    );
  }
}
