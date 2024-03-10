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


package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandC2SType;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.ServiceLoader;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;

/**
 * @see NPAMessageType
 */

@SuppressWarnings({"rawtypes"})
public final class NPACmd
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPACmd.class);

  private final Map<Class, NPAgentCommandExecutorType> executors;

  private NPACmd(
    final HashMap<Class, NPAgentCommandExecutorType> inExecutors)
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

  public static NPACmd create()
  {
    final var iterator =
      ServiceLoader.load(NPAgentCommandExecutorType.class)
        .iterator();

    final var executors =
      new HashMap<Class, NPAgentCommandExecutorType>(64);

    while (iterator.hasNext()) {
      final var executor = iterator.next();
      executors.put(executor.commandClass(), executor);
    }

    return new NPACmd(executors);
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
  public NPAResponseType execute(
    final NPAgentCommandContextType context,
    final NPAMessageType message)
    throws NPException
  {
    if (message instanceof final NPACommandC2SType<?> command) {
      final var executor = this.resolve(command);
      if (executor != null) {
        return executor.execute(context, command);
      }
    }

    LOG.debug("Received unexpected message from client: {}", message);
    throw context.fail(ERROR_PROTOCOL, errorProtocol());
  }

  /**
   * Resolve an executor for the given command.
   *
   * @param command The command
   *
   * @return An executor
   */

  public NPAgentCommandExecutorType resolve(
    final NPACommandType<?> command)
  {
    return this.executors.get(command.getClass());
  }
}
