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


package com.io7m.northpike.agent.internal.console;

import com.io7m.northpike.protocol.agent_console.NPACCommandType;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;

import java.util.Objects;

/**
 * An abstract command executor.
 *
 * @param <R> The response type
 * @param <C> The command type
 */

public abstract class NPACCmdAbstract<
  R extends NPACResponseType,
  C extends NPACCommandType<R>>
  implements NPACCommandExecutorType<R, C>
{
  private final Class<C> commandClass;

  protected NPACCmdAbstract(
    final Class<C> inCommandClass)
  {
    this.commandClass =
      Objects.requireNonNull(inCommandClass, "commandClass");
  }

  @Override
  public final Class<C> commandClass()
  {
    return this.commandClass;
  }
}
