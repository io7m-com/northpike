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


package com.io7m.northpike.toolexec.api;

import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentClear;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentOperationType;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentSet;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentUnset;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The result of evaluating a tool execution description.
 *
 * @param environmentOperations The operations to perform on the agent's environment variables
 * @param arguments             The resulting tool arguments
 * @param outputMessages        The produced output messages
 */

public record NPTEvaluationResult(
  List<NPTPEnvironmentOperationType> environmentOperations,
  List<String> arguments,
  List<String> outputMessages)
{
  /**
   * The result of evaluating a tool execution description.
   *
   * @param environmentOperations The operations to perform on the agent's environment variables
   * @param arguments             The resulting tool arguments
   * @param outputMessages        The produced output messages
   */

  public NPTEvaluationResult
  {
    environmentOperations = List.copyOf(environmentOperations);
    arguments = List.copyOf(arguments);
    outputMessages = List.copyOf(outputMessages);
  }

  /**
   * Evaluate the environment operations against the given environment.
   *
   * @param initial The environment
   *
   * @return The resulting environment
   */

  public Map<String, String> evaluateEnvironment(
    final Map<String, String> initial)
  {
    final var result = new HashMap<>(initial);
    for (final var op : this.environmentOperations) {
      switch (op) {
        case final NPTPEnvironmentClear ignored -> {
          result.clear();
        }
        case final NPTPEnvironmentSet set -> {
          result.put(set.name(), set.value());
        }
        case final NPTPEnvironmentUnset unset -> {
          result.remove(unset.name());
        }
      }
    }
    return Map.copyOf(result);
  }
}
