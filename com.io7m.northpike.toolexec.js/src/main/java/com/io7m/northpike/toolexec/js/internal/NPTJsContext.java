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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.toolexec.program.api.NPTPContextType;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentClear;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentOperationType;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentSet;
import com.io7m.northpike.toolexec.program.api.NPTPEnvironmentUnset;
import com.io7m.northpike.toolexec.program.api.NPTPVariableType;
import org.graalvm.polyglot.HostAccess;
import org.graalvm.polyglot.Value;
import org.graalvm.polyglot.proxy.ProxyArray;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.concurrent.ConcurrentLinkedQueue;

/**
 * The execution context.
 */

public final class NPTJsContext
  implements NPTPContextType
{
  private final Map<RDottedName, NPTPVariableType> variables;
  private final ConcurrentLinkedQueue<String> arguments;
  private final ArrayList<NPTPEnvironmentOperationType> environmentOps;

  /**
   * The execution context.
   *
   * @param inVariables The variables
   */

  public NPTJsContext(
    final Map<RDottedName, NPTPVariableType> inVariables)
  {
    this.environmentOps =
      new ArrayList<>();
    this.variables =
      Objects.requireNonNull(inVariables, "variables");
    this.arguments =
      new ConcurrentLinkedQueue<>();
  }

  /**
   * @return The list of environment operations
   */

  public List<NPTPEnvironmentOperationType> environmentOps()
  {
    return List.copyOf(this.environmentOps);
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
  public NPTPVariableType valueOfVariable(
    final String name)
  {
    return NPTPContextType.super.valueOfVariable(name);
  }

  @Override
  @HostAccess.Export
  public BigInteger valueOfVariableInteger(
    final String name)
  {
    return NPTPContextType.super.valueOfVariableInteger(name);
  }

  @Override
  @HostAccess.Export
  public String valueOfVariableString(
    final String name)
  {
    return NPTPContextType.super.valueOfVariableString(name);
  }

  @Override
  @HostAccess.Export
  public String[] valueOfVariableStringSet(
    final String name)
  {
    return NPTPContextType.super.valueOfVariableStringSet(name);
  }

  @Override
  @HostAccess.Export
  public ProxyArray valueOfVariableStringSetArray(
    final String name)
  {
    return new ProxyStringArray(this.valueOfVariableStringSet(name));
  }

  @Override
  @HostAccess.Export
  public NPTPVariableType valueOfVariable(
    final RDottedName name)
  {
    final var value =
      this.variables.get(Objects.requireNonNull(name, "name"));

    if (value == null) {
      throw new NoSuchElementException(
        "No such variable: '%s'".formatted(name));
    }
    return value;
  }

  @Override
  @HostAccess.Export
  public void environmentClear()
  {
    this.environmentOps.add(new NPTPEnvironmentClear());
  }

  @Override
  @HostAccess.Export
  public void environmentSet(
    final String name,
    final String value)
  {
    this.environmentOps.add(new NPTPEnvironmentSet(name, value));
  }

  @Override
  @HostAccess.Export
  public void environmentUnset(
    final String name)
  {
    this.environmentOps.add(new NPTPEnvironmentUnset(name));
  }

  @Override
  @HostAccess.Export
  public void argumentAdd(
    final String argument)
  {
    this.arguments.add(Objects.requireNonNull(argument, "argument"));
  }

  private static final class ProxyStringArray
    implements ProxyArray
  {
    private final String[] data;

    ProxyStringArray(
      final String[] startingArray)
    {
      this.data =
        Objects.requireNonNull(startingArray, "startingArray");
    }

    @Override
    public Object get(final long index)
    {
      return this.data[(int) index];
    }

    @Override
    public void set(
      final long index,
      final Value value)
    {
      this.data[(int) index] = value.toString();
    }

    @Override
    public long getSize()
    {
      return this.data.length;
    }
  }
}
