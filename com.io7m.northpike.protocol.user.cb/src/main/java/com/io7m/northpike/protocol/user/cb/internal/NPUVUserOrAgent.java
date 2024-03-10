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
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1UserOrAgentID;

/**
 * A validator.
 */

public enum NPUVUserOrAgent
  implements NPProtocolMessageValidatorType<
  NPAuditUserOrAgentType,
  NPU1UserOrAgentID>
{
  /**
   * A validator.
   */

  USER_OR_AGENT;

  @Override
  public NPU1UserOrAgentID convertToWire(
    final NPAuditUserOrAgentType message)
  {
    if (message instanceof final NPAuditUserOrAgentType.User user) {
      return new NPU1UserOrAgentID.User(new CBUUID(user.id()));
    }
    if (message instanceof final NPAuditUserOrAgentType.Agent agent) {
      return new NPU1UserOrAgentID.Agent(new CBUUID(agent.id().value()));
    }
    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPAuditUserOrAgentType convertFromWire(
    final NPU1UserOrAgentID message)
  {
    if (message instanceof final NPU1UserOrAgentID.User user) {
      return new NPAuditUserOrAgentType.User(user.fieldId().value());
    }
    if (message instanceof final NPU1UserOrAgentID.Agent agent) {
      return new NPAuditUserOrAgentType.Agent(
        new NPAgentID(agent.fieldId().value())
      );
    }
    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
