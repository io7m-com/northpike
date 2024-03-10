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

package com.io7m.northpike.preferences.api;

import com.io7m.northpike.model.tls.NPTLSConfigurationType;

import java.util.Objects;

/**
 * A server bookmark.
 *
 * @param name             The bookmark name
 * @param host             The server host
 * @param port             The server port
 * @param tlsConfiguration The TLS configuration
 * @param credentials      The credentials
 */

public record NPPreferenceServerBookmark(
  String name,
  String host,
  int port,
  NPTLSConfigurationType tlsConfiguration,
  NPPreferenceServerCredentialsType credentials)
{
  /**
   * A server bookmark.
   *
   * @param name             The bookmark name
   * @param host             The server host
   * @param port             The server port
   * @param tlsConfiguration The TLS configuration
   * @param credentials      The credentials
   */

  public NPPreferenceServerBookmark
  {
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(host, "host");
    Objects.requireNonNull(tlsConfiguration, "tlsConfiguration");
    Objects.requireNonNull(credentials, "credentials");
  }
}
