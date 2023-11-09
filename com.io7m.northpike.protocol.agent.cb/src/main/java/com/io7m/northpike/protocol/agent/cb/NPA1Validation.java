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
import com.io7m.northpike.protocol.agent.NPACommandCLoginComplete;
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
import com.io7m.northpike.protocol.agent.NPAResponseLoginChallenge;
import com.io7m.northpike.protocol.agent.NPAResponseOK;
import com.io7m.northpike.protocol.agent.NPAResponseType;
import com.io7m.northpike.protocol.agent.NPAResponseWorkOffered;
import com.io7m.northpike.protocol.agent.NPAResponseWorkSent;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCDisconnect.COMMAND_DISCONNECT;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCEnvironmentInfo.COMMAND_ENVIRONMENT_INFO;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCLogin.COMMAND_LOGIN;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCLoginComplete.COMMAND_LOGIN_COMPLETE;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemFailed.COMMAND_WORK_ITEM_FAILED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemOutput.COMMAND_WORK_ITEM_OUTPUT;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemStarted.COMMAND_WORK_ITEM_STARTED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandCWorkItemSucceeded.COMMAND_WORK_ITEM_SUCCEEDED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandSLatencyCheck.COMMAND_LATENCY_CHECK;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandSWorkOffered.COMMAND_WORK_OFFERED;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVCommandSWorkSent.COMMAND_WORK_SENT;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.agent.cb.internal.NPAVResponseLoginChallenge.RESPONSE_LOGIN_CHALLENGE;
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
    return switch (message) {
      case final NPACommandType<?> command -> toWireCommand(command);
      case final NPAResponseType response -> toWireResponse(response);
      case final NPAEventType event -> toWireEvent(event);
    };
  }

  private static ProtocolNPAv1Type toWireEvent(
    final NPAEventType event)
  {
    throw new IllegalStateException();
  }

  private static ProtocolNPAv1Type toWireResponse(
    final NPAResponseType response)
  {
    return switch (response) {
      case final NPAResponseOK r ->
        RESPONSE_OK.convertToWire(r);
      case final NPAResponseLoginChallenge r ->
        RESPONSE_LOGIN_CHALLENGE.convertToWire(r);
      case final NPAResponseError r ->
        RESPONSE_ERROR.convertToWire(r);
      case final NPAResponseLatencyCheck r ->
        RESPONSE_LATENCY_CHECK.convertToWire(r);
      case final NPAResponseWorkOffered r ->
        RESPONSE_WORK_OFFERED.convertToWire(r);
      case final NPAResponseWorkSent r ->
        RESPONSE_WORK_SENT.convertToWire(r);
    };
  }

  private static ProtocolNPAv1Type toWireCommand(
    final NPACommandType<?> command)
  {
    return switch (command) {
      case final NPACommandCLogin c ->
        COMMAND_LOGIN.convertToWire(c);
      case final NPACommandCLoginComplete c ->
        COMMAND_LOGIN_COMPLETE.convertToWire(c);
      case final NPACommandCEnvironmentInfo c ->
        COMMAND_ENVIRONMENT_INFO.convertToWire(c);
      case final NPACommandCDisconnect c ->
        COMMAND_DISCONNECT.convertToWire(c);
      case final NPACommandCWorkItemStarted c ->
        COMMAND_WORK_ITEM_STARTED.convertToWire(c);
      case final NPACommandCWorkItemFailed c ->
        COMMAND_WORK_ITEM_FAILED.convertToWire(c);
      case final NPACommandCWorkItemSucceeded c ->
        COMMAND_WORK_ITEM_SUCCEEDED.convertToWire(c);
      case final NPACommandCWorkItemOutput c ->
        COMMAND_WORK_ITEM_OUTPUT.convertToWire(c);
      case final NPACommandSLatencyCheck c ->
        COMMAND_LATENCY_CHECK.convertToWire(c);
      case final NPACommandSWorkOffered c ->
        COMMAND_WORK_OFFERED.convertToWire(c);
      case final NPACommandSWorkSent c ->
        COMMAND_WORK_SENT.convertToWire(c);
    };
  }

  @Override
  public NPAMessageType convertFromWire(
    final ProtocolNPAv1Type message)
    throws NPProtocolException
  {
    return switch (message) {
      case final NPA1CommandCLogin c ->
        COMMAND_LOGIN.convertFromWire(c);
      case final NPA1CommandCLoginComplete c ->
        COMMAND_LOGIN_COMPLETE.convertFromWire(c);
      case final NPA1CommandCEnvironmentInfo c ->
        COMMAND_ENVIRONMENT_INFO.convertFromWire(c);
      case final NPA1CommandCDisconnect c ->
        COMMAND_DISCONNECT.convertFromWire(c);
      case final NPA1CommandCWorkItemStarted c ->
        COMMAND_WORK_ITEM_STARTED.convertFromWire(c);
      case final NPA1CommandCWorkItemFailed c ->
        COMMAND_WORK_ITEM_FAILED.convertFromWire(c);
      case final NPA1CommandCWorkItemSucceeded c ->
        COMMAND_WORK_ITEM_SUCCEEDED.convertFromWire(c);
      case final NPA1CommandCWorkItemOutput c ->
        COMMAND_WORK_ITEM_OUTPUT.convertFromWire(c);
      case final NPA1CommandSLatencyCheck c ->
        COMMAND_LATENCY_CHECK.convertFromWire(c);
      case final NPA1CommandSWorkOffered c ->
        COMMAND_WORK_OFFERED.convertFromWire(c);
      case final NPA1CommandSWorkSent c ->
        COMMAND_WORK_SENT.convertFromWire(c);
      case final NPA1ResponseLoginChallenge r ->
        RESPONSE_LOGIN_CHALLENGE.convertFromWire(r);
      case final NPA1ResponseError r ->
        RESPONSE_ERROR.convertFromWire(r);
      case final NPA1ResponseOK r ->
        RESPONSE_OK.convertFromWire(r);
      case final NPA1ResponseLatencyCheck r ->
        RESPONSE_LATENCY_CHECK.convertFromWire(r);
      case final NPA1ResponseWorkOffered r ->
        RESPONSE_WORK_OFFERED.convertFromWire(r);
      case final NPA1ResponseWorkSent r ->
        RESPONSE_WORK_SENT.convertFromWire(r);
    };
  }
}
