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

package com.io7m.northpike.protocol.agent.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.cedarbridge.runtime.convenience.CBMaps;
import com.io7m.northpike.model.NPStoredException;
import com.io7m.northpike.protocol.agent.cb.NPA1Exception;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVStackTraceElement.STACK_TRACE_ELEMENT;

/**
 * A validator.
 */

public enum NPAVException
  implements NPProtocolMessageValidatorType<NPStoredException, NPA1Exception>
{
  /**
   * A validator.
   */

  EXCEPTION;

  @Override
  public NPA1Exception convertToWire(
    final NPStoredException message)
  {
    return new NPA1Exception(
      string(message.className()),
      string(message.message()),
      CBMaps.ofMapString(message.attributes()),
      CBOptionType.fromOptional(
        message.cause().map(EXCEPTION::convertToWire)),
      CBLists.ofCollection(
        message.suppressed(), EXCEPTION::convertToWire),
      CBLists.ofCollection(
        message.stackTrace(), STACK_TRACE_ELEMENT::convertToWire)
    );
  }

  @Override
  public NPStoredException convertFromWire(
    final NPA1Exception message)
  {
    return new NPStoredException(
      message.fieldClassName().value(),
      message.fieldMessage().value(),
      CBMaps.toMapString(message.fieldAttributes()),
      message.fieldCause()
        .asOptional()
        .map(EXCEPTION::convertFromWire),
      message.fieldSuppressed()
        .values()
        .stream()
        .map(EXCEPTION::convertFromWire)
        .toList(),
      message.fieldStackTrace()
        .values()
        .stream()
        .map(STACK_TRACE_ELEMENT::convertFromWire)
        .toList()
    );
  }
}
