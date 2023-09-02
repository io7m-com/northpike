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


import com.io7m.northpike.protocol.agent.NPACommandCDisconnect;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemFailed;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemOutput;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemStarted;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemSucceeded;
import com.io7m.northpike.protocol.agent.NPACommandSLatencyCheck;
import com.io7m.northpike.protocol.agent.NPACommandSWorkOffered;
import com.io7m.northpike.protocol.agent.NPACommandSWorkSent;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAEventType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseError;
import com.io7m.northpike.protocol.agent.NPAResponseLatencyCheck;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.protocol.agent.NPAResponseWorkOffered;
import com.io7m.northpike.protocol.agent.NPAResponseWorkSent;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCDisconnect.COMMAND_DISCONNECT;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCEnvironmentInfo.COMMAND_ENVIRONMENT_INFO;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCLogin.COMMAND_LOGIN;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemFailed.COMMAND_WORK_ITEM_FAILED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemOutput.COMMAND_WORK_ITEM_OUTPUT;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemStarted.COMMAND_WORK_ITEM_STARTED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemSucceeded.COMMAND_WORK_ITEM_SUCCEEDED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandSLatencyCheck.COMMAND_LATENCY_CHECK;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandSWorkOffered.COMMAND_WORK_OFFERED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandSWorkSent.COMMAND_WORK_SENT;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseOK.RESPONSE_OK;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseSLatencyCheck.RESPONSE_LATENCY_CHECK;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseSWorkOffered.RESPONSE_WORK_OFFERED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseSWorkSent.RESPONSE_WORK_SENT;

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
    if (response instanceof final NPAResponseOK r) {
      return RESPONSE_OK.convertToWire(r);
    }
    if (response instanceof final NPAResponseError r) {
      return RESPONSE_ERROR.convertToWire(r);
    }
    if (response instanceof final NPAResponseLatencyCheck r) {
      return RESPONSE_LATENCY_CHECK.convertToWire(r);
    }
    if (response instanceof final NPAResponseWorkOffered r) {
      return RESPONSE_WORK_OFFERED.convertToWire(r);
    }
    if (response instanceof final NPAResponseWorkSent r) {
      return RESPONSE_WORK_SENT.convertToWire(r);
    }

    throw new IllegalStateException("Unrecognized response: " + response);
  }

  private static ProtocolNPAv1Type toWireCommand(
    final NPACommandType<?> command)
  {
    if (command instanceof final NPACommandCLogin c) {
      return COMMAND_LOGIN.convertToWire(c);
    }
    if (command instanceof final NPACommandCEnvironmentInfo c) {
      return COMMAND_ENVIRONMENT_INFO.convertToWire(c);
    }
    if (command instanceof final NPACommandCDisconnect c) {
      return COMMAND_DISCONNECT.convertToWire(c);
    }
    if (command instanceof final NPACommandCWorkItemStarted c) {
      return COMMAND_WORK_ITEM_STARTED.convertToWire(c);
    }
    if (command instanceof final NPACommandCWorkItemFailed c) {
      return COMMAND_WORK_ITEM_FAILED.convertToWire(c);
    }
    if (command instanceof final NPACommandCWorkItemSucceeded c) {
      return COMMAND_WORK_ITEM_SUCCEEDED.convertToWire(c);
    }
    if (command instanceof final NPACommandCWorkItemOutput c) {
      return COMMAND_WORK_ITEM_OUTPUT.convertToWire(c);
    }
    if (command instanceof final NPACommandSLatencyCheck c) {
      return COMMAND_LATENCY_CHECK.convertToWire(c);
    }
    if (command instanceof final NPACommandSWorkOffered c) {
      return COMMAND_WORK_OFFERED.convertToWire(c);
    }
    if (command instanceof final NPACommandSWorkSent c) {
      return COMMAND_WORK_SENT.convertToWire(c);
    }

    throw new IllegalStateException("Unrecognized command: " + command);
  }

  @Override
  public NPAMessageType convertFromWire(
    final ProtocolNPAv1Type message)
  {
    if (message instanceof final NPA1CommandCLogin c) {
      return COMMAND_LOGIN.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandCEnvironmentInfo c) {
      return COMMAND_ENVIRONMENT_INFO.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandCDisconnect c) {
      return COMMAND_DISCONNECT.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandCWorkItemStarted c) {
      return COMMAND_WORK_ITEM_STARTED.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandCWorkItemFailed c) {
      return COMMAND_WORK_ITEM_FAILED.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandCWorkItemSucceeded c) {
      return COMMAND_WORK_ITEM_SUCCEEDED.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandCWorkItemOutput c) {
      return COMMAND_WORK_ITEM_OUTPUT.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandSLatencyCheck c) {
      return COMMAND_LATENCY_CHECK.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandSWorkOffered c) {
      return COMMAND_WORK_OFFERED.convertFromWire(c);
    }
    if (message instanceof final NPA1CommandSWorkSent c) {
      return COMMAND_WORK_SENT.convertFromWire(c);
    }

    if (message instanceof final NPA1ResponseError r) {
      return RESPONSE_ERROR.convertFromWire(r);
    }
    if (message instanceof final NPA1ResponseOK r) {
      return RESPONSE_OK.convertFromWire(r);
    }
    if (message instanceof final NPA1ResponseLatencyCheck r) {
      return RESPONSE_LATENCY_CHECK.convertFromWire(r);
    }
    if (message instanceof final NPA1ResponseWorkOffered r) {
      return RESPONSE_WORK_OFFERED.convertFromWire(r);
    }
    if (message instanceof final NPA1ResponseWorkSent r) {
      return RESPONSE_WORK_SENT.convertFromWire(r);
    }

    throw new IllegalStateException("Unrecognized message: " + message);
  }
}
