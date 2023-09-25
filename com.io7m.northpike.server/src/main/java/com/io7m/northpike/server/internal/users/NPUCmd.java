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
import com.io7m.northpike.protocol.user.NPUCommandType;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseType;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.ServiceLoader;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;

/**
 * @see NPUMessageType
 */

@SuppressWarnings({"rawtypes"})
public final class NPUCmd
{
  private final Map<Class, NPUserCommandExecutorType> executors;

  private NPUCmd(
    final HashMap<Class, NPUserCommandExecutorType> inExecutors)
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

  public static NPUCmd create()
  {
    final var iterator =
      ServiceLoader.load(NPUserCommandExecutorType.class)
        .iterator();

    final var executors =
      new HashMap<Class, NPUserCommandExecutorType>(64);

    while (iterator.hasNext()) {
      final var executor = iterator.next();
      executors.put(executor.commandClass(), executor);
    }

    return new NPUCmd(executors);
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
  public NPUResponseType execute(
    final NPUserCommandContextType context,
    final NPUMessageType message)
    throws NPException
  {
    if (message instanceof final NPUCommandType<?> command) {
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

  public NPUserCommandExecutorType resolve(
    final NPUCommandType<?> command)
  {
    return this.executors.get(command.getClass());
  }
}
