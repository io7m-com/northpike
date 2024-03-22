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
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.agents.NPAgentID;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AuditOwner;

/**
 * A validator.
 */

public enum NPUVAuditOwner
  implements NPProtocolMessageValidatorType<
  NPAuditOwnerType,
  NPU1AuditOwner>
{
  /**
   * A validator.
   */

  AUDIT_OWNER;

  @Override
  public NPU1AuditOwner convertToWire(
    final NPAuditOwnerType message)
  {
    return switch (message) {
      case final NPAuditOwnerType.User user -> {
        yield new NPU1AuditOwner.User(new CBUUID(user.id()));
      }
      case final NPAuditOwnerType.Agent agent -> {
        yield new NPU1AuditOwner.Agent(new CBUUID(agent.id().value()));
      }
      case final NPAuditOwnerType.Server ignored -> {
        yield new NPU1AuditOwner.Server();
      }
    };
  }

  @Override
  public NPAuditOwnerType convertFromWire(
    final NPU1AuditOwner message)
  {
    return switch (message) {
      case final NPU1AuditOwner.User user -> {
        yield new NPAuditOwnerType.User(user.fieldId().value());
      }
      case final NPU1AuditOwner.Agent agent -> {
        yield new NPAuditOwnerType.Agent(new NPAgentID(agent.fieldId().value()));
      }
      case final NPU1AuditOwner.Server server -> {
        yield new NPAuditOwnerType.Server();
      }
    };
  }
}
