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


package com.io7m.northpike.agent.workexec.local;

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.agent.workexec.local.cb.NWEException;
import com.io7m.northpike.agent.workexec.local.cb.NWEStackTraceElement;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.model.NPStoredStackTraceElement;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;

/**
 * Functions to translate messages in the workexec protocol.
 */

public final class NPWEMessages
{
  private NPWEMessages()
  {

  }

  /**
   * Convert an exception from the on-wire form.
   *
   * @param e The exception
   *
   * @return The exception
   */

  public static NPStoredException exceptionOfWire(
    final NWEException e)
  {
    return new NPStoredException(
      e.fieldClassName().value(),
      e.fieldMessage().value(),
      CBMaps.toMapString(e.fieldAttributes()),
      e.fieldCause().asOptional().map(NPWEMessages::exceptionOfWire),
      CBLists.toList(e.fieldSuppressed(), NPWEMessages::exceptionOfWire),
      CBLists.toList(e.fieldStackTrace(), NPWEMessages::elementOfWire)
    );
  }

  /**
   * Convert a stack trace element from the on-wire form.
   *
   * @param e The stack trace element
   *
   * @return The stack trace element
   */

  public static NPStoredStackTraceElement elementOfWire(
    final NWEStackTraceElement e)
  {
    return new NPStoredStackTraceElement(
      e.fieldClassLoader().value(),
      e.fieldModuleName().value(),
      e.fieldModuleName().value(),
      e.fieldDeclaringClass().value(),
      e.fieldMethodName().value(),
      e.fieldFileName().value(),
      (int) e.fieldLineNumber().value()
    );
  }


  /**
   * Convert an exception to the on-wire form.
   *
   * @param e The exception
   *
   * @return The on-wire exception
   */

  public static NWEException exceptionToWire(
    final NPStoredException e)
  {
    return new NWEException(
      string(e.className()),
      string(e.message()),
      CBMaps.ofMapString(e.attributes()),
      CBOptionType.fromOptional(
        e.cause().map(NPWEMessages::exceptionToWire)
      ),
      CBLists.ofCollection(e.suppressed(), NPWEMessages::exceptionToWire),
      CBLists.ofCollection(e.stackTrace(), NPWEMessages::elementToWire)
    );
  }

  /**
   * Convert a stack trace element to the on-wire form.
   *
   * @param e The stack trace element
   *
   * @return The on-wire stack trace element
   */

  public static NWEStackTraceElement elementToWire(
    final NPStoredStackTraceElement e)
  {
    return new NWEStackTraceElement(
      string(e.classLoader()),
      string(e.moduleName()),
      string(e.moduleVersion()),
      string(e.declaringClass()),
      string(e.methodName()),
      string(e.fileName()),
      unsigned32(e.lineNumber())
    );
  }
}
