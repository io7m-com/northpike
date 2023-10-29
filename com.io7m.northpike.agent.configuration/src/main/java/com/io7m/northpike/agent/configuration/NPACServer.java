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

import com.io7m.northpike.model.agents.NPAgentServerID;
import com.io7m.northpike.tls.NPTLSConfigurationType;

import java.util.Objects;

/**
 * A server configuration for an agent.
 *
 * @param id               The ID
 * @param hostName         The host name
 * @param port             The port
 * @param messageSizeLimit The message size limit
 * @param tlsConfiguration The TLS configuration
 */

public record NPACServer(
  NPAgentServerID id,
  String hostName,
  int port,
  int messageSizeLimit,
  NPTLSConfigurationType tlsConfiguration)
{
  /**
   * A server configuration for an agent.
   *
   * @param id               The ID
   * @param hostName         The host name
   * @param port             The port
   * @param messageSizeLimit The message size limit
   * @param tlsConfiguration The TLS configuration
   */

  public NPACServer
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(hostName, "hostName");
    Objects.requireNonNull(tlsConfiguration, "tlsConfiguration");
  }
}
