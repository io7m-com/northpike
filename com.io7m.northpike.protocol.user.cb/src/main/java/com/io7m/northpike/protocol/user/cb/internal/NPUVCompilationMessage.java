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

package com.io7m.northpike.protocol.user.cb.internal;

import com.io7m.northpike.model.NPCompilationMessage;
import com.io7m.northpike.model.NPCompilationMessage.Kind;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1CompilationMessage;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;
import static com.io7m.cedarbridge.runtime.api.CBCore.unsigned32;

/**
 * A validator.
 */

public enum NPUVCompilationMessage
  implements NPProtocolMessageValidatorType<NPCompilationMessage, NPU1CompilationMessage>
{
  /**
   * A validator.
   */

  COMPILATION_MESSAGE;

  @Override
  public NPU1CompilationMessage convertToWire(
    final NPCompilationMessage message)
  {
    return new NPU1CompilationMessage(
      string(message.kind().name()),
      unsigned32(message.line()),
      unsigned32(message.column()),
      string(message.message())
    );
  }

  @Override
  public NPCompilationMessage convertFromWire(
    final NPU1CompilationMessage message)
  {
    return new NPCompilationMessage(
      Kind.valueOf(message.fieldKind().value()),
      (int) message.fieldLine().value(),
      (int) message.fieldColumn().value(),
      message.fieldMessage().value()
    );
  }
}
