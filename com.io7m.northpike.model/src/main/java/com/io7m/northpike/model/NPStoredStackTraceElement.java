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

import static java.util.Objects.requireNonNull;
import static java.util.Objects.requireNonNullElse;

/**
 * A stack trace element.
 *
 * @param classLoader    The class loader (or "&lt;unnamed-classloader>")
 * @param moduleName     The module name (or "&lt;unnamed-module>")
 * @param moduleVersion  The module version (or "&lt;unversioned>")
 * @param declaringClass The declaring class
 * @param methodName     The method name
 * @param fileName       The file name
 * @param lineNumber     The line number
 *
 * @see StackTraceElement
 */

public record NPStoredStackTraceElement(
  String classLoader,
  String moduleName,
  String moduleVersion,
  String declaringClass,
  String methodName,
  String fileName,
  int lineNumber)
{
  /**
   * A stack trace element.
   *
   * @param classLoader    The class loader (or "&lt;unnamed-classloader>")
   * @param moduleName     The module name (or "&lt;unnamed-module>")
   * @param moduleVersion  The module version (or "&lt;unversioned>")
   * @param declaringClass The declaring class
   * @param methodName     The method name
   * @param fileName       The file name
   * @param lineNumber     The line number
   *
   * @see StackTraceElement
   */

  public NPStoredStackTraceElement
  {
    requireNonNull(classLoader, "classLoader");
    requireNonNull(moduleName, "moduleName");
    requireNonNull(moduleVersion, "moduleVersion");
    requireNonNull(declaringClass, "declaringClass");
    requireNonNull(methodName, "methodName");
    requireNonNull(fileName, "fileName");
  }

  /**
   * Create a stored version of the given stack trace element.
   *
   * @param e The element
   *
   * @return The stored element
   */

  public static NPStoredStackTraceElement ofElement(
    final StackTraceElement e)
  {
    requireNonNull(e, "Element");

    return new NPStoredStackTraceElement(
      requireNonNullElse(e.getClassLoaderName(), "<unnamed-classloader>"),
      requireNonNullElse(e.getModuleName(), "<unnamed-module>"),
      requireNonNullElse(e.getModuleVersion(), "<no-module-version>"),
      e.getClassName(),
      e.getMethodName(),
      requireNonNullElse(e.getFileName(), "<unknown-file>"),
      e.getLineNumber()
    );
  }

  @Override
  public String toString()
  {
    return new StringBuilder(128)
      .append(this.classLoader)
      .append('/')
      .append(this.moduleName)
      .append('@')
      .append(this.moduleVersion)
      .append('/')
      .append(this.declaringClass)
      .append('.')
      .append(this.methodName)
      .append('(')
      .append(this.fileName)
      .append(':')
      .append(this.lineNumber)
      .append(')')
      .toString();
  }
}
