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


package com.io7m.northpike.toolexecj.runner;

import java.util.List;
import java.util.Map;

/**
 * The result of evaluating a tool execution description.
 *
 * @param environment    The agent's resulting environment variables
 * @param arguments      The resulting tool arguments
 * @param outputMessages The produced output messages
 */

public record NPTJEvaluation(
  Map<String, String> environment,
  List<String> arguments,
  List<String> outputMessages)
{
  /**
   * The result of evaluating a tool execution description.
   *
   * @param environment    The agent's resulting environment variables
   * @param arguments      The resulting tool arguments
   * @param outputMessages The produced output messages
   */

  public NPTJEvaluation
  {
    environment = Map.copyOf(environment);
    arguments = List.copyOf(arguments);
    outputMessages = List.copyOf(outputMessages);
  }
}
