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

import com.io7m.lanark.core.RDottedName;
import com.io7m.northpike.model.NPAgentLabelMatchType;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.cb.NPU1AgentLabelMatch;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPUVAgentLabelMatch
  implements NPProtocolMessageValidatorType<NPAgentLabelMatchType, NPU1AgentLabelMatch>
{
  /**
   * A validator.
   */

  AGENT_LABEL_MATCH;

  @Override
  public NPU1AgentLabelMatch convertToWire(
    final NPAgentLabelMatchType message)
  {
    if (message instanceof NPAgentLabelMatchType.AnyLabel) {
      return new NPU1AgentLabelMatch.AnyLabel();
    }

    if (message instanceof final NPAgentLabelMatchType.And and) {
      return new NPU1AgentLabelMatch.And(
        AGENT_LABEL_MATCH.convertToWire(and.e0()),
        AGENT_LABEL_MATCH.convertToWire(and.e1())
      );
    }

    if (message instanceof final NPAgentLabelMatchType.Or or) {
      return new NPU1AgentLabelMatch.Or(
        AGENT_LABEL_MATCH.convertToWire(or.e0()),
        AGENT_LABEL_MATCH.convertToWire(or.e1())
      );
    }

    if (message instanceof final NPAgentLabelMatchType.Specific specific) {
      return new NPU1AgentLabelMatch.Specific(string(specific.name().value()));
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }

  @Override
  public NPAgentLabelMatchType convertFromWire(
    final NPU1AgentLabelMatch message)
  {
    if (message instanceof NPU1AgentLabelMatch.AnyLabel) {
      return NPAgentLabelMatchType.AnyLabel.ANY_LABEL;
    }

    if (message instanceof final NPU1AgentLabelMatch.And and) {
      return new NPAgentLabelMatchType.And(
        AGENT_LABEL_MATCH.convertFromWire(and.fieldE0()),
        AGENT_LABEL_MATCH.convertFromWire(and.fieldE1())
      );
    }

    if (message instanceof final NPU1AgentLabelMatch.Or or) {
      return new NPAgentLabelMatchType.Or(
        AGENT_LABEL_MATCH.convertFromWire(or.fieldE0()),
        AGENT_LABEL_MATCH.convertFromWire(or.fieldE1())
      );
    }

    if (message instanceof final NPU1AgentLabelMatch.Specific specific) {
      return new NPAgentLabelMatchType.Specific(
        new RDottedName(specific.fieldName().value())
      );
    }

    throw new IllegalStateException(
      "Unrecognized message: %s".formatted(message)
    );
  }
}
