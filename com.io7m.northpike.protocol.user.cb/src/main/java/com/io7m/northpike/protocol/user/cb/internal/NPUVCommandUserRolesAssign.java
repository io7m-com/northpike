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
import com.io7m.northpike.protocol.user.NPUCommandUserRolesAssign;
import com.io7m.northpike.protocol.user.cb.NPU1CommandUserRolesAssign;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVCommandUserRolesAssign
  implements NPProtocolMessageValidatorType<NPUCommandUserRolesAssign, NPU1CommandUserRolesAssign>
{
  /**
   * A validator.
   */

  COMMAND_USER_ROLES_ASSIGN;

  @Override
  public NPU1CommandUserRolesAssign convertToWire(
    final NPUCommandUserRolesAssign message)
  {
    return new NPU1CommandUserRolesAssign(
      new CBUUID(message.messageID()),
      new CBUUID(message.user()),
      CBLists.ofCollection(message.roles(), x -> string(x.value().value()))
    );
  }

  @Override
  public NPUCommandUserRolesAssign convertFromWire(
    final NPU1CommandUserRolesAssign message)
  {
    return new NPUCommandUserRolesAssign(
      message.fieldMessageId().value(),
      message.fieldUser().value(),
      CBSets.toSet(message.fieldRoles(), x -> MRoleName.of(x.value()))
    );
  }
}
