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


package com.io7m.northpike.protocol.agent_console;

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;

import java.util.Objects;
import java.util.Optional;
import java.util.UUID;

/**
 * An agent.
 *
 * @param messageID     The message ID
 * @param correlationID The command that prompted this response
 * @param results       The results
 */

public record NPACResponseAgent(
  UUID messageID,
  UUID correlationID,
  Optional<Result> results)
  implements NPACResponseType
{
  /**
   * An agent.
   *
   * @param messageID     The message ID
   * @param correlationID The command that prompted this response
   * @param results       The results
   */

  public NPACResponseAgent
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(correlationID, "correlationID");
    Objects.requireNonNull(results, "summaries");
  }

  /**
   * The result.
   *
   * @param name         The agent name
   * @param publicKey    The public key
   * @param server       The server associated with the agent
   * @param workExecutor The work executor associated with the agent
   */

  public record Result(
    NPAgentLocalName name,
    NPAgentKeyPublicType publicKey,
    Optional<NPAgentServerID> server,
    Optional<NPAWorkExecutorConfiguration> workExecutor)
  {
    /**
     * The result.
     *
     * @param name         The agent name
     * @param publicKey    The public key
     * @param server       The server associated with the agent
     * @param workExecutor The work executor associated with the agent
     */

    public Result
    {
      Objects.requireNonNull(name, "name");
      Objects.requireNonNull(publicKey, "publicKey");
      Objects.requireNonNull(server, "server");
      Objects.requireNonNull(workExecutor, "workExecutor");
    }
  }
}
