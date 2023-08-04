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


package com.io7m.northpike.protocol.agent;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.UUID;

/**
 * Send environment information.
 *
 * @param messageID            The ID of this message
 * @param environmentVariables The environment variables
 * @param systemProperties     The system properties
 */

public record NPACommandCEnvironmentInfo(
  UUID messageID,
  Map<String, String> environmentVariables,
  Map<String, String> systemProperties)
  implements NPACommandC2SType<NPAResponseOK>
{
  /**
   * Send environment information.
   *
   * @param messageID            The ID of this message
   * @param environmentVariables The environment variables
   * @param systemProperties     The system properties
   */

  public NPACommandCEnvironmentInfo
  {
    Objects.requireNonNull(messageID, "messageID");
    Objects.requireNonNull(environmentVariables, "environmentVariables");
    Objects.requireNonNull(systemProperties, "systemProperties");
  }

  /**
   * Create a new message with a generated message ID.
   *
   * @param environmentVariables The environment variables
   * @param systemProperties     The system properties
   *
   * @return The message
   */

  public static NPACommandCEnvironmentInfo of(
    final Map<String, String> environmentVariables,
    final Map<String, String> systemProperties)
  {
    return new NPACommandCEnvironmentInfo(
      UUID.randomUUID(),
      environmentVariables,
      systemProperties
    );
  }

  /**
   * Create a new message with a generated message ID, reading environment
   * variables and system properties from the current runtime.
   *
   * @return The message
   */

  public static NPACommandCEnvironmentInfo of()
  {
    final var props =
      new HashMap<String, String>();
    final var sysProps =
      System.getProperties();

    for (final var key : sysProps.stringPropertyNames()) {
      props.put(key, sysProps.getProperty(key));
    }

    return of(System.getenv(), props);
  }

  @Override
  public Class<NPAResponseOK> responseClass()
  {
    return NPAResponseOK.class;
  }
}
