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
import com.io7m.northpike.protocol.user.NPUCommandToolSearchNext;
import com.io7m.northpike.protocol.user.NPUResponseToolSearch;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.tools.api.NPToolFactoryType;

import java.util.Comparator;
import java.util.UUID;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorApiMisuse;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_SEARCH_NOT_STARTED;

/**
 * @see NPUCommandToolSearchNext
 */

public final class NPUCmdToolSearchNext
  extends NPUCmdAbstract<
  NPUResponseToolSearch,
  NPUCommandToolSearchNext>
{
  /**
   * @see NPUCommandToolSearchNext
   */

  public NPUCmdToolSearchNext()
  {
    super(NPUCommandToolSearchNext.class);
  }

  @Override
  public NPUResponseToolSearch execute(
    final NPUserCommandContextType context,
    final NPUCommandToolSearchNext command)
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

    final var paged =
      context.property(NPSearchPage.class)
        .orElseThrow(() -> {
          return context.fail(ERROR_SEARCH_NOT_STARTED, errorApiMisuse());
        });

    final var pagedNext =
      paged.next();

    final var toolPage =
      services.optionalServices(NPToolFactoryType.class)
        .stream()
        .sorted(Comparator.comparing((NPToolFactoryType o) -> o.toolName()))
        .skip(pagedNext.itemOffset())
        .limit(paged.pageSize())
        .map(NPToolFactoryType::summary)
        .toList();

    return new NPUResponseToolSearch(
      UUID.randomUUID(),
      command.messageID(),
      new NPPage<>(
        toolPage,
        (int) pagedNext.pageIndex(),
        (int) pagedNext.pageCount(),
        pagedNext.itemOffset()
      )
    );
  }
}
