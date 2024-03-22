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

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandToolGet;
import com.io7m.northpike.protocol.user.NPUResponseToolGet;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.tools.api.NPToolFactoryType;

import java.util.Objects;
import java.util.UUID;

/**
 * @see NPUCommandToolGet
 */

public final class NPUCmdToolGet
  extends NPUCmdAbstract<
  NPUResponseToolGet,
  NPUCommandToolGet>
{
  /**
   * @see NPUCommandToolGet
   */

  public NPUCmdToolGet()
  {
    super(NPUCommandToolGet.class);
  }

  @Override
  public NPUResponseToolGet execute(
    final NPUserCommandContextType context,
    final NPUCommandToolGet command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.TOOLS.object(),
      NPSecAction.READ.action()
    );

    final var services =
      context.services();

    return new NPUResponseToolGet(
      UUID.randomUUID(),
      command.messageID(),
      services.optionalServices(NPToolFactoryType.class)
        .stream()
        .filter(p -> Objects.equals(p.toolName(), command.name()))
        .map(NPToolFactoryType::toolDescription)
        .findFirst()
    );
  }
}
