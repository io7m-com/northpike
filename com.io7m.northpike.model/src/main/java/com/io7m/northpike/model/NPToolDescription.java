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

import com.io7m.verona.core.VersionRange;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A tool description.
 *
 * @param name              The tool name
 * @param description       The tool description
 * @param versions          The supported tool versions
 * @param defaultExecutions The default executions
 */

public record NPToolDescription(
  NPToolName name,
  String description,
  VersionRange versions,
  Map<NPToolExecutionName, List<String>> defaultExecutions)
{
  /**
   * A tool description.
   *
   * @param name              The tool name
   * @param description       The tool description
   * @param versions          The supported tool versions
   * @param defaultExecutions The default executions
   */

  public NPToolDescription
  {
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(description, "description");
    Objects.requireNonNull(versions, "versions");
    Objects.requireNonNull(defaultExecutions, "defaultExecutions");
  }

  /**
   * @return A summary of the description
   */

  public NPToolSummary summary()
  {
    return new NPToolSummary(
      this.name,
      this.description
    );
  }
}
