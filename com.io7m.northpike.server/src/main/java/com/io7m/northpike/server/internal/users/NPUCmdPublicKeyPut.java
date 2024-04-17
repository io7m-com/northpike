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


package com.io7m.northpike.server.internal.users;

import com.io7m.northpike.database.api.NPDatabaseQueriesPublicKeysType;
import com.io7m.northpike.keys.NPPublicKeys;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandPublicKeyPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.security.NPSecurity;

/**
 * @see NPUCommandPublicKeyPut
 */

public final class NPUCmdPublicKeyPut
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandPublicKeyPut>
{
  /**
   * @see NPUCommandPublicKeyPut
   */

  public NPUCmdPublicKeyPut()
  {
    super(NPUCommandPublicKeyPut.class);
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandPublicKeyPut command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.PUBLIC_KEYS.object(),
      NPSecAction.WRITE.action()
    );

    final var keys =
      NPPublicKeys.decodeString(command.key());

    try (var transaction = context.transaction()) {
      transaction.setOwner(new NPAuditOwnerType.User(user.userId()));

      for (final var key : keys) {
        transaction.queries(NPDatabaseQueriesPublicKeysType.PublicKeyPutType.class)
          .execute(key);
      }
      transaction.commit();
    }

    return NPUResponseOK.createCorrelated(command);
  }
}
