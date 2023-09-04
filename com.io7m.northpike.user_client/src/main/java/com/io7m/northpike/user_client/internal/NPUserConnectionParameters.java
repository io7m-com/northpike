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


package com.io7m.northpike.user_client.internal;

import com.io7m.idstore.model.IdName;
import com.io7m.northpike.tls.NPTLSConfigurationType;
import com.io7m.northpike.user_client.api.NPUserClientConfiguration;

import java.net.InetSocketAddress;
import java.util.Objects;

/**
 * The connection parameters.
 *
 * @param configuration The base client configuration
 * @param userName      The username
 * @param password      The password
 * @param address       The server address
 * @param tls           The TLS configuration
 */

public record NPUserConnectionParameters(
  NPUserClientConfiguration configuration,
  IdName userName,
  String password,
  InetSocketAddress address,
  NPTLSConfigurationType tls)
{
  /**
   * The connection parameters.
   *
   * @param configuration The base client configuration
   * @param userName      The username
   * @param password      The password
   * @param address       The server address
   * @param tls           The TLS configuration
   */

  public NPUserConnectionParameters
  {
    Objects.requireNonNull(userName, "userName");
    Objects.requireNonNull(password, "password");
    Objects.requireNonNull(configuration, "configuration");
    Objects.requireNonNull(address, "address");
    Objects.requireNonNull(tls, "tls");
  }
}
