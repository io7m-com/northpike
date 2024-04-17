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

import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.api.NPRepositoriesPagedType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseRepositorySearch;
import com.io7m.northpike.server.internal.security.NPSecurity;

import java.util.UUID;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;

/**
 * @see NPUCommandRepositorySearchBegin
 */

public final class NPUCmdRepositorySearchBegin
  extends NPUCmdAbstract<NPUResponseRepositorySearch, NPUCommandRepositorySearchBegin>
{
  /**
   * @see NPUCommandRepositorySearchBegin
   */

  public NPUCmdRepositorySearchBegin()
  {
    super(NPUCommandRepositorySearchBegin.class);
  }

  @Override
  public NPUResponseRepositorySearch execute(
    final NPUserCommandContextType context,
    final NPUCommandRepositorySearchBegin command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.REPOSITORIES.object(),
      NPSecAction.READ.action()
    );

    try (var transaction = context.transaction(NORTHPIKE_READ_ONLY)) {
      final var paged =
        transaction.queries(NPDatabaseQueriesRepositoriesType.RepositoryListType.class)
          .execute(NPDatabaseUnit.UNIT);

      context.setProperty(NPRepositoriesPagedType.class, paged);

      final var page =
        paged.pageCurrent(transaction)
          .map(NPRepositoryDescription::summary);

      return new NPUResponseRepositorySearch(
        UUID.randomUUID(),
        command.messageID(),
        page
      );
    }
  }
}
