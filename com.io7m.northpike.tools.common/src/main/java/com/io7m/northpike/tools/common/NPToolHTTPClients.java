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


package com.io7m.northpike.tools.common;

import com.io7m.northpike.model.NPVersion;

import java.net.http.HttpClient;
import java.net.http.HttpRequest;

/**
 * A factory of HTTP clients.
 */

public final class NPToolHTTPClients
{
  private NPToolHTTPClients()
  {

  }

  /**
   * A function that sets the user agent for a request.
   *
   * @param builder The request builder
   */

  public static void setUserAgent(
    final HttpRequest.Builder builder)
  {
    builder.setHeader("User-Agent", userAgent());
  }

  /**
   * @return The user agent
   */

  public static String userAgent()
  {
    return "com.io7m.northpike %s (%s)"
      .formatted(NPVersion.MAIN_VERSION, NPVersion.MAIN_BUILD);
  }

  /**
   * @return A new HTTP client
   */

  public static HttpClient create()
  {
    return HttpClient.newBuilder()
      .followRedirects(HttpClient.Redirect.NORMAL)
      .build();
  }
}
