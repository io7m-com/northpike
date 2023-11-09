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

package com.io7m.northpike.server.api;

import com.io7m.northpike.model.tls.NPTLSConfigurationType;

import java.net.InetAddress;
import java.net.URI;
import java.util.Objects;

/**
 * Configuration information for the archive service.
 *
 * @param localAddress The local address used for the archive service
 * @param localPort    The local port used for the archive service
 * @param tls          The TLS configuration
 * @param advertiseURI The base URI advertised to agents
 */

public record NPServerArchiveConfiguration(
  InetAddress localAddress,
  int localPort,
  NPTLSConfigurationType tls,
  URI advertiseURI)
{
  /**
   * Configuration information for the archive service.
   *
   * @param localAddress The local address used for the archive service
   * @param localPort    The local port used for the archive service
   * @param tls          The TLS configuration
   * @param advertiseURI The base URI advertised to agents
   */

  public NPServerArchiveConfiguration
  {
    Objects.requireNonNull(localAddress, "localAddress");
    Objects.requireNonNull(tls, "tls");
    Objects.requireNonNull(advertiseURI, "advertiseURI");
  }
}
