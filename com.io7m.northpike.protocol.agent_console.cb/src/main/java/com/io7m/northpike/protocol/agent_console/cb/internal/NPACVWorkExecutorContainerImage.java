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


package com.io7m.northpike.protocol.agent_console.cb.internal;

import com.io7m.cedarbridge.runtime.api.CBCore;
import com.io7m.cedarbridge.runtime.api.CBOptionType;
import com.io7m.cedarbridge.runtime.api.CBString;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1WorkExecutorContainerImage;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVWorkExecutorContainerImage
  implements NPProtocolMessageValidatorType<
  NPAWorkExecutorContainerImage, NPAC1WorkExecutorContainerImage>
{
  /**
   * A validator.
   */

  WORK_EXECUTOR_CONTAINER_IMAGE;

  @Override
  public NPAC1WorkExecutorContainerImage convertToWire(
    final NPAWorkExecutorContainerImage message)
  {
    return new NPAC1WorkExecutorContainerImage(
      string(message.registry()),
      string(message.name()),
      string(message.tag()),
      CBOptionType.fromOptional(
        message.hash()
          .map(CBCore::string)
      )
    );
  }

  @Override
  public NPAWorkExecutorContainerImage convertFromWire(
    final NPAC1WorkExecutorContainerImage message)
  {
    return new NPAWorkExecutorContainerImage(
      message.fieldRegistry().value(),
      message.fieldName().value(),
      message.fieldTag().value(),
      message.fieldHash().asOptional().map(CBString::value)
    );
  }
}
