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


package com.io7m.northpike.agent.api;

import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.agents.NPAgentLocalDescription;
import com.io7m.northpike.model.agents.NPAgentServerDescription;

import java.util.Objects;

/**
 * The configuration for an agent.
 *
 * @param workExecutor The work executor configuration
 * @param agent        The local description of the agent
 * @param server       The description of the server
 */

public record NPAgentConfiguration(
  NPAWorkExecutorConfiguration workExecutor,
  NPAgentLocalDescription agent,
  NPAgentServerDescription server)
{
  /**
   * The configuration for an agent.
   *
   * @param workExecutor The work executor configuration
   * @param agent        The local description of the agent
   * @param server       The description of the server
   */

  public NPAgentConfiguration
  {
    Objects.requireNonNull(workExecutor, "workExecutor");
    Objects.requireNonNull(agent, "agent");
    Objects.requireNonNull(server, "server");
  }
}
