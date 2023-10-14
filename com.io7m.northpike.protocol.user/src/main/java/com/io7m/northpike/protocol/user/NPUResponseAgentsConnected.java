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


package com.io7m.northpike.protocol.user;

import com.io7m.northpike.model.agents.NPAgentID;

import java.util.Objects;
import java.util.Set;
import java.util.UUID;

/**
 * An agent list retrieval.
 *
 * @param messageID     The message ID
 * @param correlationID The command that prompted this response
 * @param agents        The agents
 */

public record NPUResponseAgentsConnected(
  UUID messageID,
  UUID correlationID,
  Set<NPAgentID> agents)
  implements NPUResponseType
{
  /**
   * An agent list retrieval.
   *
   * @param messageID     The message ID
   * @param correlationID The command that prompted this response
   * @param agents        The agents
   */

  public NPUResponseAgentsConnected
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(correlationID, "correlationID");
    Objects.requireNonNull(agents, "agents");
  }

  /**
   * Create a response with a random message ID, with a correlation
   * ID matched to the given command.
   *
   * @param command The command
   * @param agents  The agents
   *
   * @return An OK response
   */

  public static NPUResponseAgentsConnected createCorrelated(
    final NPUCommandType<?> command,
    final Set<NPAgentID> agents)
  {
    return new NPUResponseAgentsConnected(
      UUID.randomUUID(),
      command.messageID(),
      agents
    );
  }
}
