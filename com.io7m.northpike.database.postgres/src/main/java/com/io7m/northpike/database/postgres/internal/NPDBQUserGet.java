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


package com.io7m.northpike.database.postgres.internal;


import com.io7m.idstore.model.IdName;
import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType.GetType;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPUser;
import org.jooq.DSLContext;
import org.jooq.Record3;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;

import static com.io7m.northpike.database.postgres.internal.tables.Users.USERS;

/**
 * Retrieve a user.
 */

public final class NPDBQUserGet
  extends NPDBQAbstract<UUID, Optional<NPUser>>
  implements GetType
{
  private static final Service<UUID, Optional<NPUser>, GetType> SERVICE =
    new Service<>(GetType.class, NPDBQUserGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQUserGet(
    final NPDatabaseTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPDBQueryProviderType provider()
  {
    return () -> SERVICE;
  }


  @Override
  protected Optional<NPUser> onExecute(
    final DSLContext context,
    final UUID id)
    throws NPDatabaseException
  {
    final var query =
      context.select(
        USERS.ID,
        USERS.NAME,
        USERS.ROLES
      ).from(USERS)
      .where(USERS.ID.eq(id));

    recordQuery(query);
    return query.fetchOptional().map(NPDBQUserGet::mapUser);
  }

  private static NPUser mapUser(
    final Record3<UUID, String, String[]> r)
  {
    return new NPUser(
      r.get(USERS.ID),
      new IdName(r.get(USERS.NAME)),
      new MSubject(ofRoles(r.get(USERS.ROLES)))
    );
  }

  private static Set<MRoleName> ofRoles(
    final String[] strings)
  {
    final var results = new HashSet<MRoleName>(strings.length);
    for (final var role : strings) {
      results.add(new MRoleName(new RDottedName(role)));
    }
    return results;
  }
}
