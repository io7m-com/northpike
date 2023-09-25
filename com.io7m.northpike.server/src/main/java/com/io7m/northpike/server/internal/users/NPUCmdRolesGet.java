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
import com.io7m.northpike.protocol.user.NPUCommandRolesGet;
import com.io7m.northpike.protocol.user.NPUResponseRolesGet;

import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;


/**
 * @see NPUCommandRolesGet
 */

public final class NPUCmdRolesGet
  extends NPUCmdAbstract<NPUResponseRolesGet, NPUCommandRolesGet>
{
  /**
   * @see NPUCommandRolesGet
   */

  public NPUCmdRolesGet()
  {
    super(NPUCommandRolesGet.class);
  }

  @Override
  public NPUResponseRolesGet execute(
    final NPUserCommandContextType context,
    final NPUCommandRolesGet command)
    throws NPException
  {
    context.onAuthenticationRequire();

    try (var connection = context.databaseConnection()) {
      try (var transaction = connection.openTransaction()) {
        final var get =
          transaction.queries(NPDatabaseQueriesUsersType.GetType.class);

        final var targetUser =
          get.execute(command.user())
            .orElseThrow(() -> {
              return context.fail(ERROR_NONEXISTENT, errorNonexistent());
            });

        return new NPUResponseRolesGet(
          UUID.randomUUID(),
          command.messageID(),
          targetUser.subject().roles()
        );
      }
    }
  }
}
