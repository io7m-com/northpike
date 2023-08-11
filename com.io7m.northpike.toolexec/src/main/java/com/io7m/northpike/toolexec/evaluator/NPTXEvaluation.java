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


package com.io7m.northpike.toolexec.evaluator;

import com.io7m.northpike.toolexec.checker.NPTXTypeChecked;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The result of evaluating a tool execution description.
 *
 * @param source      The type-checked source
 * @param environment The agent's resulting environment variables
 * @param arguments   The resulting tool arguments
 */

public record NPTXEvaluation(
  NPTXTypeChecked source,
  Map<String, String> environment,
  List<String> arguments)
{
  /**
   * The result of evaluating a tool execution description.
   *
   * @param source      The type-checked source
   * @param environment The agent's resulting environment variables
   * @param arguments   The resulting tool arguments
   */

  public NPTXEvaluation
  {
    Objects.requireNonNull(source, "source");
    Objects.requireNonNull(environment, "environment");
    Objects.requireNonNull(arguments, "arguments");

    environment = Map.copyOf(environment);
    arguments = List.copyOf(arguments);
  }
}
