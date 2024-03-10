/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.model;

/**
 * The standard service ports.
 */

public final class NPStandardServicePorts
{
  private NPStandardServicePorts()
  {

  }

  /**
   * @return The standard port for the user service
   */

  public static int userServicePort()
  {
    return 20050;
  }

  /**
   * @return The standard port for the user service with TLS
   */

  public static int userServicePortWithTLS()
  {
    return 21050;
  }

  /**
   * @return The standard port for the archive service
   */

  public static int archiveServicePort()
  {
    return 20049;
  }

  /**
   * @return The standard port for the archive service with TLS
   */

  public static int archiveServicePortWithTLS()
  {
    return 21049;
  }

  /**
   * @return The standard port for the agent service
   */

  public static int agentServicePort()
  {
    return 20048;
  }

  /**
   * @return The standard port for the agent service with TLS
   */

  public static int agentServicePortWithTLS()
  {
    return 21048;
  }
}
