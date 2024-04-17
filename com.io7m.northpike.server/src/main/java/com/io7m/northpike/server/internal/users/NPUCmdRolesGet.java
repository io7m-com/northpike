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


import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesGet;
import com.io7m.northpike.protocol.user.NPUResponseUserRolesGet;

import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;


/**
 * @see NPUCommandUserRolesGet
 */

public final class NPUCmdRolesGet
  extends NPUCmdAbstract<NPUResponseUserRolesGet, NPUCommandUserRolesGet>
{
  /**
   * @see NPUCommandUserRolesGet
   */

  public NPUCmdRolesGet()
  {
    super(NPUCommandUserRolesGet.class);
  }

  @Override
  public NPUResponseUserRolesGet execute(
    final NPUserCommandContextType context,
    final NPUCommandUserRolesGet command)
    throws NPException
  {
    context.onAuthenticationRequire();

    try (var transaction = context.transaction(NORTHPIKE_READ_ONLY)) {
      final var get =
        transaction.queries(NPDatabaseQueriesUsersType.GetType.class);

      final var targetUser =
        get.execute(command.user())
          .orElseThrow(() -> {
            return context.fail(ERROR_NONEXISTENT, errorNonexistent());
          });

      return new NPUResponseUserRolesGet(
        UUID.randomUUID(),
        command.messageID(),
        targetUser.subject().roles()
      );
    }
  }
}
