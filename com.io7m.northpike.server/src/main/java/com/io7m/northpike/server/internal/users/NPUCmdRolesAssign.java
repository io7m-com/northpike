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

import com.io7m.idstore.model.IdName;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPUser;
import com.io7m.northpike.model.security.NPSecRole;
import com.io7m.northpike.protocol.user.NPUCommandUserRolesAssign;
import com.io7m.northpike.protocol.user.NPUResponseOK;

import java.util.HashSet;
import java.util.Set;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorOperationNotPermitted;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_OPERATION_NOT_PERMITTED;


/**
 * @see NPUCommandUserRolesAssign
 */

public final class NPUCmdRolesAssign
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandUserRolesAssign>
{
  /**
   * @see NPUCommandUserRolesAssign
   */

  public NPUCmdRolesAssign()
  {
    super(NPUCommandUserRolesAssign.class);
  }

  private static NPUResponseOK assignRoles(
    final NPUserCommandContextType context,
    final NPUCommandUserRolesAssign command,
    final NPUser user,
    final Set<MRoleName> rolesGiven)
    throws NPException
  {
    try (var transaction = context.transaction()) {
      transaction.setOwner(new NPAuditOwnerType.User(user.userId()));

      final var put =
        transaction.queries(NPDatabaseQueriesUsersType.PutType.class);
      final var get =
        transaction.queries(NPDatabaseQueriesUsersType.GetType.class);

      final var targetUser =
        get.execute(command.user())
          .orElseGet(() -> {
            return new NPUser(
              command.user(),
              new IdName("X-%s".formatted(command.user())),
              new MSubject(rolesGiven)
            );
          });

      final var newRoles = new HashSet<>(targetUser.subject().roles());
      newRoles.addAll(rolesGiven);
      put.execute(
        new NPUser(
          targetUser.userId(),
          targetUser.name(),
          new MSubject(newRoles)
        )
      );

      transaction.commit();
      return NPUResponseOK.createCorrelated(command);
    }
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandUserRolesAssign command)
    throws NPException
  {
    final var user =
      context.onAuthenticationRequire();
    final var subject =
      user.subject();

    /*
     * Does the current subject have all the roles that are being given away,
     * or is the current subject an administrator?
     */

    final var rolesGiven =
      command.roles();
    final var rolesHeld =
      subject.roles();

    if (rolesHeld.contains(NPSecRole.ADMINISTRATOR.role())) {
      return assignRoles(context, command, user, rolesGiven);
    }

    if (rolesHeld.containsAll(rolesGiven)) {
      return assignRoles(context, command, user, rolesGiven);
    }

    throw context.fail(
      ERROR_OPERATION_NOT_PERMITTED,
      errorOperationNotPermitted()
    );
  }
}
