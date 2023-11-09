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

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPValidityException;
import com.io7m.northpike.model.agents.NPAgentKeyPairFactoryEd448;
import com.io7m.northpike.model.agents.NPAgentKeyPublicType;
import com.io7m.northpike.protocol.agent_console.cb.NPAC1AgentPublicKey;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.cedarbridge.runtime.api.CBCore.string;

/**
 * A validator.
 */

public enum NPACVAgentPublicKey
  implements NPProtocolMessageValidatorType<NPAgentKeyPublicType, NPAC1AgentPublicKey>
{
  /**
   * A validator.
   */

  AGENT_PUBLIC_KEY;

  @Override
  public NPAC1AgentPublicKey convertToWire(
    final NPAgentKeyPublicType message)
  {
    return new NPAC1AgentPublicKey(
      string(message.algorithm()),
      string(message.asText())
    );
  }

  @Override
  public NPAgentKeyPublicType convertFromWire(
    final NPAC1AgentPublicKey message)
    throws NPProtocolException
  {
    return switch (message.fieldAlgorithm().value()) {
      case "Ed448" -> {
        try {
          yield new NPAgentKeyPairFactoryEd448()
            .parsePublicKeyFromText(message.fieldPublicKey().value());
        } catch (final NPException e) {
          throw new NPProtocolException(
            e.getMessage(),
            e,
            e.errorCode(),
            e.attributes(),
            e.remediatingAction()
          );
        }
      }
      default -> {
        throw new NPValidityException("Unrecognized algorithm.");
      }
    };
  }
}
