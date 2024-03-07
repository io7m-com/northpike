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

package com.io7m.northpike.toolexec.program.api;

import com.io7m.lanark.core.RDottedName;

import java.math.BigInteger;
import java.util.Set;

/**
 * A program's execution context.
 */

public interface NPTPContextType
{
  /**
   * @param name The variable name
   *
   * @return The value of the variable
   */

  NPTPVariableType valueOfVariable(
    RDottedName name);

  /**
   * @param name The variable name
   *
   * @return The value of the variable
   */

  default NPTPVariableType valueOfVariable(
    final String name)
  {
    return this.valueOfVariable(new RDottedName(name));
  }

  /**
   * @param name The variable name
   *
   * @return The value of the integer typed variable
   */

  default BigInteger valueOfVariableInteger(
    final RDottedName name)
  {
    return switch (this.valueOfVariable(name)) {
      case final NPTPVariableInteger i -> {
        yield i.value();
      }
      case final NPTPVariableString ignored ->
        throw errorWrongType(name, "string");
      case final NPTPVariableStringSet ignored ->
        throw errorWrongType(name, "string-set");
      case final NPTPVariableBoolean ignored ->
        throw errorWrongType(name, "boolean");
    };
  }

  /**
   * @param name The variable name
   *
   * @return The value of the integer typed variable
   */

  default BigInteger valueOfVariableInteger(
    final String name)
  {
    return this.valueOfVariableInteger(new RDottedName(name));
  }

  /**
   * @param name The variable name
   *
   * @return The value of the boolean typed variable
   */

  default boolean valueOfVariableBoolean(
    final RDottedName name)
  {
    return switch (this.valueOfVariable(name)) {
      case final NPTPVariableBoolean i -> {
        yield i.value();
      }
      case final NPTPVariableString ignored ->
        throw errorWrongType(name, "string");
      case final NPTPVariableStringSet ignored ->
        throw errorWrongType(name, "string-set");
      case final NPTPVariableInteger ignored ->
        throw errorWrongType(name, "integer");
    };
  }

  /**
   * @param name The variable name
   *
   * @return The value of the boolean typed variable
   */

  default boolean valueOfVariableBoolean(
    final String name)
  {
    return this.valueOfVariableBoolean(new RDottedName(name));
  }

  /**
   * @param name The variable name
   *
   * @return The value of the string typed variable
   */

  default String valueOfVariableString(
    final RDottedName name)
  {
    return switch (this.valueOfVariable(name)) {
      case final NPTPVariableString s -> {
        yield s.value();
      }
      case final NPTPVariableInteger ignored ->
        throw errorWrongType(name, "integer");
      case final NPTPVariableStringSet ignored ->
        throw errorWrongType(name, "string-set");
      case final NPTPVariableBoolean ignored ->
        throw errorWrongType(name, "boolean");
    };
  }

  /**
   * @param name The variable name
   *
   * @return The value of the string typed variable
   */

  default String valueOfVariableString(
    final String name)
  {
    return this.valueOfVariableString(new RDottedName(name));
  }

  /**
   * @param name The variable name
   *
   * @return The value of the string-set typed variable
   */

  default Set<String> valueOfVariableStringSet(
    final RDottedName name)
  {
    return switch (this.valueOfVariable(name)) {
      case final NPTPVariableStringSet ss -> {
        yield ss.value();
      }
      case final NPTPVariableInteger ignored ->
        throw errorWrongType(name, "integer");
      case final NPTPVariableString ignored ->
        throw errorWrongType(name, "string");
      case final NPTPVariableBoolean ignored ->
        throw errorWrongType(name, "boolean");
    };
  }

  private static IllegalArgumentException errorWrongType(
    final RDottedName name,
    final String expectedType)
  {
    return new IllegalArgumentException(
      "Type error: The variable %s is of type '%s'".formatted(
        name,
        expectedType));
  }

  /**
   * @param name The variable name
   *
   * @return The value of the string-set typed variable
   */

  default String[] valueOfVariableStringSet(
    final String name)
  {
    final var strings =
      this.valueOfVariableStringSet(new RDottedName(name));
    final var output =
      new String[strings.size()];

    int index = 0;
    for (final var s : strings) {
      output[index] = s;
      ++index;
    }
    return output;
  }

  /**
   * @param name The variable name
   *
   * @return The value of the string-set typed variable
   */

  Object valueOfVariableStringSetArray(
    String name);

  /**
   * Clear the environment entirely.
   */

  void environmentClear();

  /**
   * Set an environment variable.
   *
   * @param name  The variable name
   * @param value The variable value
   */

  void environmentSet(
    String name,
    String value);

  /**
   * Remove an environment variable.
   *
   * @param name The variable name
   */

  void environmentUnset(
    String name);

  /**
   * Add an argument to the output.
   *
   * @param argument The argument
   */

  void argumentAdd(
    String argument);
}
