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
import java.util.UUID;

/**
 * Convert a login challenge to a new agent. The public key of the agent
 * will be taken from the login challenge.
 *
 * @param messageID      The message ID
 * @param loginChallenge The login challenge
 * @param agent          The ID of the agent to create
 * @param name           The name of the agent to create
 */

public record NPUCommandAgentLoginChallengeAgentCreate(
  UUID messageID,
  UUID loginChallenge,
  NPAgentID agent,
  String name)
  implements NPUCommandType<NPUResponseOK>
{
  /**
   * Convert a login challenge to a new agent. The public key of the agent
   * will be taken from the login challenge.
   *
   * @param messageID      The message ID
   * @param loginChallenge The login challenge
   * @param agent          The ID of the agent to create
   * @param name           The name of the agent to create
   */

  public NPUCommandAgentLoginChallengeAgentCreate
  {
    Objects.requireNonNull(messageID, "messageId");
    Objects.requireNonNull(loginChallenge, "loginChallenge");
    Objects.requireNonNull(agent, "agent");
    Objects.requireNonNull(name, "name");
  }

  @Override
  public Class<NPUResponseOK> responseClass()
  {
    return NPUResponseOK.class;
  }
}
