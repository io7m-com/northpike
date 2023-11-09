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

import java.net.InetAddress;
import java.util.Objects;

/**
 * An agent console configuration.
 *
 * @param address   The address to which to bind the console
 * @param port      The TCP port to which to bind the console
 * @param accessKey The access key used to access the console
 */

public record NPAgentConsoleConfiguration(
  InetAddress address,
  int port,
  String accessKey)
{
  /**
   * An agent console configuration.
   *
   * @param address   The address to which to bind the console
   * @param port      The TCP port to which to bind the console
   * @param accessKey The access key used to access the console
   */

  public NPAgentConsoleConfiguration
  {
    Objects.requireNonNull(address, "address");
    Objects.requireNonNull(accessKey, "accessKey");
  }
}
