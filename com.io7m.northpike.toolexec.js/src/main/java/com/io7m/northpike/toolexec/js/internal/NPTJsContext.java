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


package com.io7m.northpike.toolexec.js.internal;

import com.io7m.northpike.toolexec.program.api.NPTPContextType;
import org.graalvm.polyglot.HostAccess;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * The execution context.
 */

public final class NPTJsContext
  implements NPTPContextType
{
  private final Map<String, String> environment;
  private final ConcurrentLinkedQueue<String> arguments;

  /**
   * The execution context.
   *
   * @param env The initial environment
   */

  public NPTJsContext(
    final Map<String, String> env)
  {
    this.environment =
      new ConcurrentHashMap<>(env);
    this.arguments =
      new ConcurrentLinkedQueue<>();
  }

  /**
   * @return The environment
   */

  public Map<String, String> environment()
  {
    return Map.copyOf(this.environment);
  }

  /**
   * @return The list of resulting arguments
   */

  public List<String> arguments()
  {
    return List.copyOf(this.arguments);
  }

  @Override
  @HostAccess.Export
  public void environmentClear()
  {
    this.environment.clear();
  }

  @Override
  @HostAccess.Export
  public void environmentPut(
    final String name,
    final String value)
  {
    this.environment.put(
      Objects.requireNonNull(name, "name"),
      Objects.requireNonNull(value, "value")
    );
  }

  @Override
  @HostAccess.Export
  public void environmentRemove(
    final String name)
  {
    this.environment.remove(Objects.requireNonNull(name, "name"));
  }

  @Override
  @HostAccess.Export
  public void argumentAdd(
    final String argument)
  {
    this.arguments.add(Objects.requireNonNull(argument, "argument"));
  }
}
