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

import com.io7m.idstore.protocol.user.IdUResponseLogin;
import com.io7m.idstore.user_client.api.IdUClientCredentials;
import com.io7m.idstore.user_client.api.IdUClientException;
import com.io7m.northpike.database.api.NPDatabaseQueriesUsersType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.security.NPSecurity;

import java.util.Map;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorAuthentication;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_AUTHENTICATION;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;

/**
 * @see NPUCommandLogin
 */

public final class NPUCmdLogin
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandLogin>
{
  /**
   * @see NPUCommandLogin
   */

  public NPUCmdLogin()
  {
    super(NPUCommandLogin.class);
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandLogin command)
    throws NPException
  {
    try (var resources = NPServerResources.createResources()) {

      final var connection =
        resources.add(context.databaseConnection());
      final var client =
        resources.add(context.createIdstoreClient());
      final var transaction =
        resources.add(connection.openTransaction());

      final IdUResponseLogin response =
        (IdUResponseLogin) client.loginOrElseThrow(
          new IdUClientCredentials(
            command.name().value(),
            command.password(),
            context.idstoreLoginURI(),
            Map.of()
          ),
          IdUClientException::ofError
        );

      final var user =
        transaction.queries(NPDatabaseQueriesUsersType.GetType.class)
          .execute(response.user().id())
          .orElseThrow(() -> {
            return context.fail(ERROR_AUTHENTICATION, errorAuthentication());
          });

      NPSecurity.check(
        user.userId(),
        user.subject(),
        NPSecObject.SERVER.object(),
        NPSecAction.LOGIN.action()
      );

      context.onAuthenticationComplete(user.userId());
    } catch (final Exception e) {
      recordSpanException(e);
      throw context.fail(e, ERROR_AUTHENTICATION, errorAuthentication());
    }

    return NPUResponseOK.createCorrelated(command);
  }
}
