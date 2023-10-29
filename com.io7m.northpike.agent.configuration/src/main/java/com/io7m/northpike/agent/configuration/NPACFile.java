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


package com.io7m.northpike.agent.configuration;

import com.io7m.northpike.model.NPMapValidation;
import com.io7m.northpike.model.NPValidityException;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import com.io7m.northpike.model.agents.NPAgentServerID;

import java.util.Map;

/**
 * An agent configuration file.
 *
 * @param servers The servers
 * @param agents  The agents
 */

public record NPACFile(
  Map<NPAgentServerID, NPACServer> servers,
  Map<NPAgentLocalName, NPACAgent> agents)
{
  /**
   * An agent configuration file.
   *
   * @param servers The servers
   * @param agents  The agents
   */

  public NPACFile
  {
    NPMapValidation.check(servers, NPACServer::id);
    NPMapValidation.check(agents, NPACAgent::name);

    for (final var agent : agents.values()) {
      if (!servers.containsKey(agent.server())) {
        throw new NPValidityException(
          "Agent %s refers to nonexistent server %s"
            .formatted(agent.name(), agent.server())
        );
      }
    }

    agents = Map.copyOf(agents);
    servers = Map.copyOf(servers);
  }
}
