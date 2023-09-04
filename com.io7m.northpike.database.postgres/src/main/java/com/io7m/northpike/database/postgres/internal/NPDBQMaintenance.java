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

import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MRoleName;
import com.io7m.northpike.database.api.NPDatabaseQueriesMaintenanceType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.database.postgres.internal.NPDBQueryProviderType.Service;
import com.io7m.northpike.model.security.NPSecRole;
import org.jooq.DSLContext;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static com.io7m.northpike.database.api.NPDatabaseUnit.UNIT;
import static com.io7m.northpike.database.postgres.internal.Tables.USERS;

/**
 * A query to run maintenance.
 */

public final class NPDBQMaintenance
  extends NPDBQAbstract<NPDatabaseUnit, NPDatabaseUnit>
  implements NPDatabaseQueriesMaintenanceType.ExecuteType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPDBQMaintenance.class);

  private static final Service<NPDatabaseUnit, NPDatabaseUnit, ExecuteType> SERVICE =
    new Service<>(ExecuteType.class, NPDBQMaintenance::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPDBQMaintenance(
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
  protected NPDatabaseUnit onExecute(
    final DSLContext context,
    final NPDatabaseUnit parameters)
  {
    updateUserRoles(context);
    return UNIT;
  }

  private static void updateUserRoles(
    final DSLContext context)
  {
    final var roleNamesWithoutLogin =
      NPSecRole.allRoles()
        .stream()
        .filter(role -> role != NPSecRole.LOGIN)
        .map(NPSecRole::role)
        .map(MRoleName::value)
        .map(RDottedName::value)
        .toList();

    final var rolesArray = new String[roleNamesWithoutLogin.size()];
    roleNamesWithoutLogin.toArray(rolesArray);

    final var adminRoleName =
      NPSecRole.ADMINISTRATOR.role().value().value();
    final var adminRoleNameA =
      new String[]{adminRoleName};

    final var updated =
      context.update(USERS)
        .set(USERS.ROLES, rolesArray)
        .where(USERS.ROLES.contains(adminRoleNameA))
        .execute();

    LOG.debug(
      "Updated {} users with admin roles.",
      Integer.valueOf(updated)
    );
  }
}
