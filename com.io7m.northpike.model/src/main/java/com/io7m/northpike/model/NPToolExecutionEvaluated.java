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

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A fully evaluated tool execution, suitable for running on a specific agent.
 *
 * @param environment   The complete set of environment variables
 * @param toolReference The tool reference
 * @param command       The command arguments
 */

public record NPToolExecutionEvaluated(
  NPToolReference toolReference,
  Map<String, String> environment,
  List<String> command)
{
  /**
   * A fully evaluated tool execution, suitable for running on a specific agent.
   *
   * @param environment   The complete set of environment variables
   * @param toolReference The tool reference
   * @param command       The command arguments
   */

  public NPToolExecutionEvaluated
  {
    Objects.requireNonNull(environment, "environment");
    Objects.requireNonNull(toolReference, "toolReference");
    Objects.requireNonNull(command, "command");
  }
}
