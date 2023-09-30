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


import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.NPUser;
import org.jooq.DSLContext;

import java.util.Arrays;
import java.util.Set;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.USERS;
import static com.io7m.northpike.strings.NPStringConstants.USER;
import static com.io7m.northpike.strings.NPStringConstants.USER_ID;

/**
 * Update a user.
 */

public final class NPDBQUserPut
  extends NPDBQAbstract<NPUser, NPDatabaseUnit>
  implements NPDatabaseQueriesUsersType.PutType
{
  private static final Service<NPUser, NPDatabaseUnit, PutType> SERVICE =
    new Service<>(PutType.class, NPDBQUserPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQUserPut(
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

  private static String[] roleSetToStringArray(
    final Set<MRoleName> targetRoles)
  {
    final var roles = new String[targetRoles.size()];
    var index = 0;
    for (final var role : targetRoles) {
      roles[index] = role.value().value();
      ++index;
    }
    Arrays.sort(roles);
    return roles;
  }

  @Override
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPUser user)
  {
    this.setAttribute(USER, user.name().value());
    this.setAttribute(USER_ID, user.userId().toString());

    final var query =
      context.insertInto(USERS)
        .set(USERS.U_NAME, user.name().value())
        .set(USERS.U_ID, user.userId())
        .set(USERS.U_ROLES, roleSetToStringArray(user.subject().roles()))
        .onConflict(USERS.U_ID)
        .doUpdate()
        .set(USERS.U_NAME, user.name().value())
        .set(USERS.U_ID, user.userId())
        .set(USERS.U_ROLES, roleSetToStringArray(user.subject().roles()));

    recordQuery(query);
    query.execute();
    return UNIT;
  }
}
