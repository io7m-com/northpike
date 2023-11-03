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

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandType;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.ServiceLoader;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;

/**
 * @see NPACMessageType
 */

@SuppressWarnings({"rawtypes"})
public final class NPACCmd
{
  private final Map<Class, NPACCommandExecutorType> executors;

  private NPACCmd(
    final HashMap<Class, NPACCommandExecutorType> inExecutors)
  {
    this.executors = Map.copyOf(
      Objects.requireNonNull(inExecutors, "executors")
    );
  }

  /**
   * Create a new command executor, loading executors from {@link ServiceLoader}.
   *
   * @return A new command executor
   */

  public static NPACCmd create()
  {
    final var iterator =
      ServiceLoader.load(NPACCommandExecutorType.class)
        .iterator();

    final var executors =
      new HashMap<Class, NPACCommandExecutorType>(64);

    while (iterator.hasNext()) {
      final var executor = iterator.next();
      executors.put(executor.commandClass(), executor);
    }

    return new NPACCmd(executors);
  }

  /**
   * Execute a message.
   *
   * @param context The command context
   * @param message The message
   *
   * @return The result of executing the message
   *
   * @throws NPException On errors
   */

  @SuppressWarnings({"unchecked"})
  public NPACResponseType execute(
    final NPACCommandContextType context,
    final NPACMessageType message)
    throws NPException
  {
    if (message instanceof final NPACCommandType<?> command) {
      final var executor = this.resolve(command);
      if (executor != null) {
        return executor.execute(context, command);
      }
    }

    throw context.fail(ERROR_PROTOCOL, errorProtocol());
  }

  /**
   * Resolve an executor for the given command.
   *
   * @param command The command
   *
   * @return An executor
   */

  public NPACCommandExecutorType resolve(
    final NPACCommandType<?> command)
  {
    return this.executors.get(command.getClass());
  }
}
