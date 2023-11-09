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

import com.io7m.cedarbridge.runtime.api.CBUUID;
import com.io7m.cedarbridge.runtime.convenience.CBLists;
import com.io7m.northpike.model.agents.NPAgentLabelName;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelDelete;
import com.io7m.northpike.protocol.user.cb.NPU1CommandAgentLabelDelete;

import java.util.stream.Collectors;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVCommandAgentLabelDelete
  implements NPProtocolMessageValidatorType<NPUCommandAgentLabelDelete, NPU1CommandAgentLabelDelete>
{
  /**
   * A validator.
   */

  COMMAND_AGENT_LABEL_DELETE;

  @Override
  public NPU1CommandAgentLabelDelete convertToWire(
    final NPUCommandAgentLabelDelete message)
  {
    return new NPU1CommandAgentLabelDelete(
      new CBUUID(message.messageID()),
      CBLists.ofCollection(message.labels(), n -> string(n.toString()))
    );
  }

  @Override
  public NPUCommandAgentLabelDelete convertFromWire(
    final NPU1CommandAgentLabelDelete message)
  {
    return new NPUCommandAgentLabelDelete(
      message.fieldMessageId().value(),
      message.fieldNames()
        .values()
        .stream()
        .map(s -> NPAgentLabelName.of(s.value()))
        .collect(Collectors.toUnmodifiableSet())
    );
  }
}
