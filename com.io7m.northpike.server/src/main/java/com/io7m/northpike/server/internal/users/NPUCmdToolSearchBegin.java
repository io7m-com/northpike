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
import com.io7m.northpike.model.NPPage;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandToolSearchBegin;
import com.io7m.northpike.protocol.user.NPUResponseToolSearch;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.tools.api.NPToolFactoryType;

import java.util.Comparator;
import java.util.UUID;
import java.util.stream.Stream;

/**
 * @see NPUCommandToolSearchBegin
 */

public final class NPUCmdToolSearchBegin
  extends NPUCmdAbstract<
  NPUResponseToolSearch,
  NPUCommandToolSearchBegin>
{
  /**
   * @see NPUCommandToolSearchBegin
   */

  public NPUCmdToolSearchBegin()
  {
    super(NPUCommandToolSearchBegin.class);
  }

  @Override
  public NPUResponseToolSearch execute(
    final NPUserCommandContextType context,
    final NPUCommandToolSearchBegin command)
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

    final Stream<? extends NPToolFactoryType> toolStream =
      services.optionalServices(NPToolFactoryType.class)
        .stream()
        .sorted(Comparator.comparing((NPToolFactoryType o) -> o.toolName()));

    final var toolCount =
      toolStream.count();
    final var toolPageCount =
      Math.max(1L, toolCount / command.parameters().pageSize());

    final var toolPage =
      services.optionalServices(NPToolFactoryType.class)
        .stream()
        .sorted(Comparator.comparing((NPToolFactoryType o) -> o.toolName()))
        .limit(command.parameters().pageSize())
        .map(NPToolFactoryType::summary)
        .toList();

    context.setProperty(
      NPSearchPage.class,
      new NPSearchPage(
        1L,
        command.parameters().pageSize(),
        toolPageCount,
        0L,
        toolCount
      )
    );

    return new NPUResponseToolSearch(
      UUID.randomUUID(),
      command.messageID(),
      new NPPage<>(
        toolPage,
        1,
        (int) toolPageCount,
        0L
      )
    );
  }

}
