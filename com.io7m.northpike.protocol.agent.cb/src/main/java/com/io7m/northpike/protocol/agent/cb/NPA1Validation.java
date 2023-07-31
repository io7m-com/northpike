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

package com.io7m.northpike.protocol.agent.cb;


import com.io7m.northpike.protocol.agent.NPACommandLogin;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAEventType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLogin;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandLogin.COMMAND_LOGIN;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseLogin.RESPONSE_LOGIN;

/**
 * Functions to translate between the core command set and the Agent v1
 * Cedarbridge encoding command set.
 */

public final class NPA1Validation
  implements NPProtocolMessageValidatorType<NPAMessageType, ProtocolNPAv1Type>
{
  /**
   * Functions to translate between the core command set and the Agent v1
   * Cedarbridge encoding command set.
   */

  public NPA1Validation()
  {

  }

  @Override
  public ProtocolNPAv1Type convertToWire(
    final NPAMessageType message)
    throws NPProtocolException
  {
    if (message instanceof final NPACommandType<?> command) {
      return toWireCommand(command);
    }
    if (message instanceof final NPAResponseType response) {
      return toWireResponse(response);
    }
    if (message instanceof final NPAEventType event) {
      return toWireEvent(event);
    }
    throw new IllegalStateException();
  }

  private static ProtocolNPAv1Type toWireEvent(
    final NPAEventType event)
  {
    throw new IllegalStateException();
  }

  private static ProtocolNPAv1Type toWireResponse(
    final NPAResponseType response)
  {
    if (response instanceof final NPAResponseLogin r) {
      return RESPONSE_LOGIN.convertToWire(r);
    }
    if (response instanceof final NPAResponseError r) {
      return RESPONSE_ERROR.convertToWire(r);
    }

    throw new IllegalStateException();
  }

  private static ProtocolNPAv1Type toWireCommand(
    final NPACommandType<?> command)
  {
    if (command instanceof final NPACommandLogin c) {
      return COMMAND_LOGIN.convertToWire(c);
    }

    throw new IllegalStateException();
  }

  @Override
  public NPAMessageType convertFromWire(
    final ProtocolNPAv1Type message)
  {
    if (message instanceof final NPA1CommandLogin c) {
      return COMMAND_LOGIN.convertFromWire(c);
    }
    if (message instanceof final NPA1ResponseError r) {
      return RESPONSE_ERROR.convertFromWire(r);
    }
    if (message instanceof final NPA1ResponseLogin r) {
      return RESPONSE_LOGIN.convertFromWire(r);
    }
    throw new IllegalStateException();
  }
}
