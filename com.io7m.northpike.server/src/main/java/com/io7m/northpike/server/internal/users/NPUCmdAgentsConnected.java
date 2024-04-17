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
import com.io7m.northpike.model.agents.NPAgentConnected;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandAgentsConnected;
import com.io7m.northpike.protocol.user.NPUResponseAgentsConnected;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.security.NPSecurity;

import java.util.Set;

/**
 * @see NPUCommandAgentsConnected
 */

public final class NPUCmdAgentsConnected
  extends NPUCmdAbstract<NPUResponseAgentsConnected, NPUCommandAgentsConnected>
{
  /**
   * @see NPUCommandAgentsConnected
   */

  public NPUCmdAgentsConnected()
  {
    super(NPUCommandAgentsConnected.class);
  }

  @Override
  public NPUResponseAgentsConnected execute(
    final NPUserCommandContextType context,
    final NPUCommandAgentsConnected command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.AGENTS.object(),
      NPSecAction.ENUMERATE.action()
    );

    final Set<NPAgentConnected> connected =
      context.services()
        .requireService(NPAgentServiceType.class)
        .findAgentsConnected();

    return NPUResponseAgentsConnected.createCorrelated(command, connected);
  }
}
