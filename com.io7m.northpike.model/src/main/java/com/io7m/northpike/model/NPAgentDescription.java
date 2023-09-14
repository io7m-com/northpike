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


package com.io7m.northpike.model;

import com.io7m.lanark.core.RDottedName;

import java.util.Map;
import java.util.Objects;

/**
 * A description of an agent.
 *
 * @param id                   The agent ID
 * @param name                 The name
 * @param accessKey            The access key
 * @param environmentVariables The environment variables
 * @param systemProperties     The system properties
 * @param labels               The labels applied to the agent
 */

public record NPAgentDescription(
  NPAgentID id,
  String name,
  NPKey accessKey,
  Map<String, String> environmentVariables,
  Map<String, String> systemProperties,
  Map<RDottedName, NPAgentLabel> labels)
{
  /**
   * A description of an agent.
   *
   * @param id                   The agent ID
   * @param name                 The name
   * @param accessKey            The access key
   * @param environmentVariables The environment variables
   * @param systemProperties     The system properties
   * @param labels               The labels applied to the agent
   */

  public NPAgentDescription
  {
    Objects.requireNonNull(id, "id");
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(accessKey, "accessKey");
    Objects.requireNonNull(environmentVariables, "environmentVariables");
    Objects.requireNonNull(systemProperties, "systemProperties");
    Objects.requireNonNull(labels, "labels");

    NPMapValidation.check(labels, NPAgentLabel::name);
  }

  /**
   * @return A summary of this description
   */

  public NPAgentSummary summary()
  {
    return new NPAgentSummary(
      this.id,
      this.name
    );
  }
}
