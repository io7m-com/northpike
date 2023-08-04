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

import java.util.List;
import java.util.Objects;

/**
 * Custom arguments for a tool.
 *
 * @param name      The name of the arguments
 * @param toolName  The name of the tool for which these arguments are intended
 * @param arguments The arguments
 */

public record NPToolArguments(
  RDottedName name,
  RDottedName toolName,
  List<String> arguments)
{
  /**
   * Custom arguments for a tool.
   *
   * @param name      The name of the arguments
   * @param toolName  The name of the tool for which these arguments are intended
   * @param arguments The arguments
   */

  public NPToolArguments
  {
    Objects.requireNonNull(name, "name");
    Objects.requireNonNull(toolName, "toolName");
    Objects.requireNonNull(arguments, "arguments");
  }
}
