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

package com.io7m.northpike.protocol.user.cb;


import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryGet;
import com.io7m.northpike.protocol.user.NPUCommandRepositoryPut;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchNext;
import com.io7m.northpike.protocol.user.NPUCommandRepositorySearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandRolesAssign;
import com.io7m.northpike.protocol.user.NPUCommandRolesGet;
import com.io7m.northpike.protocol.user.NPUCommandRolesRevoke;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionPut;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUCommandType;
import com.io7m.northpike.protocol.user.NPUEventType;
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUResponseAgentLabelSearch;
import com.io7m.northpike.protocol.user.NPUResponseError;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.protocol.user.NPUResponseRepositoryGet;
import com.io7m.northpike.protocol.user.NPUResponseRepositorySearch;
import com.io7m.northpike.protocol.user.NPUResponseRolesGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionGet;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionSearch;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUResponseType;

import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelDelete.COMMAND_AGENT_LABEL_DELETE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelGet.COMMAND_AGENT_LABEL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelPut.COMMAND_AGENT_LABEL_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchBegin.COMMAND_AGENT_LABEL_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchNext.COMMAND_AGENT_LABEL_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandAgentLabelSearchPrevious.COMMAND_AGENT_LABEL_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandDisconnect.COMMAND_DISCONNECT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandLogin.COMMAND_LOGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryGet.COMMAND_REPOSITORY_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositoryPut.COMMAND_REPOSITORY_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositorySearchBegin.COMMAND_REPOSITORY_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositorySearchNext.COMMAND_REPOSITORY_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRepositorySearchPrevious.COMMAND_REPOSITORY_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRolesAssign.COMMAND_ROLES_ASSIGN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRolesGet.COMMAND_ROLES_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandRolesRevoke.COMMAND_ROLES_REVOKE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionGet.COMMAND_TOOL_EXECUTION_DESCRIPTION_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionPut.COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionSearchBegin.COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionSearchNext.COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionSearchPrevious.COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVCommandToolExecutionDescriptionValidate.COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentLabelGet.RESPONSE_AGENT_LABEL_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseAgentLabelSearch.RESPONSE_AGENT_LABEL_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseOK.RESPONSE_OK;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseRepositoryGet.RESPONSE_REPOSITORY_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseRepositorySearch.RESPONSE_REPOSITORY_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseRolesGet.RESPONSE_ROLES_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolExecutionDescriptionGet.RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolExecutionDescriptionSearch.RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH;
import static com.io7m.northpike.protocol.user.cb.internal.NPUVResponseToolExecutionDescriptionValidate.RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE;

/**
 * Functions to translate between the core command set and the Agent v1
 * Cedarbridge encoding command set.
 */

public final class NPU1Validation
  implements NPProtocolMessageValidatorType<NPUMessageType, ProtocolNPUv1Type>
{
  /**
   * Functions to translate between the core command set and the Agent v1
   * Cedarbridge encoding command set.
   */

  public NPU1Validation()
  {

  }

  @Override
  public ProtocolNPUv1Type convertToWire(
    final NPUMessageType message)
    throws NPProtocolException
  {
    if (message instanceof final NPUCommandType<?> command) {
      return toWireCommand(command);
    }
    if (message instanceof final NPUResponseType response) {
      return toWireResponse(response);
    }
    if (message instanceof final NPUEventType event) {
      return toWireEvent(event);
    }
    throw new IllegalStateException();
  }

  private static ProtocolNPUv1Type toWireEvent(
    final NPUEventType event)
  {
    throw new IllegalStateException();
  }

  private static ProtocolNPUv1Type toWireResponse(
    final NPUResponseType response)
  {
    if (response instanceof final NPUResponseOK r) {
      return RESPONSE_OK.convertToWire(r);
    }
    if (response instanceof final NPUResponseError r) {
      return RESPONSE_ERROR.convertToWire(r);
    }
    if (response instanceof final NPUResponseRepositoryGet r) {
      return RESPONSE_REPOSITORY_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseRepositorySearch r) {
      return RESPONSE_REPOSITORY_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseRolesGet r) {
      return RESPONSE_ROLES_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentLabelGet r) {
      return RESPONSE_AGENT_LABEL_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseAgentLabelSearch r) {
      return RESPONSE_AGENT_LABEL_SEARCH.convertToWire(r);
    }
    if (response instanceof final NPUResponseToolExecutionDescriptionValidate r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertToWire(r);
    }
    if (response instanceof final NPUResponseToolExecutionDescriptionGet r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET.convertToWire(r);
    }
    if (response instanceof final NPUResponseToolExecutionDescriptionSearch r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH.convertToWire(r);
    }

    throw new IllegalStateException("Unrecognized response: " + response);
  }

  private static ProtocolNPUv1Type toWireCommand(
    final NPUCommandType<?> command)
  {
    if (command instanceof final NPUCommandLogin c) {
      return COMMAND_LOGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandDisconnect c) {
      return COMMAND_DISCONNECT.convertToWire(c);
    }

    if (command instanceof final NPUCommandRepositoryPut c) {
      return COMMAND_REPOSITORY_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositoryGet c) {
      return COMMAND_REPOSITORY_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositorySearchBegin c) {
      return COMMAND_REPOSITORY_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositorySearchNext c) {
      return COMMAND_REPOSITORY_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandRepositorySearchPrevious c) {
      return COMMAND_REPOSITORY_SEARCH_PREVIOUS.convertToWire(c);
    }

    if (command instanceof final NPUCommandRolesAssign c) {
      return COMMAND_ROLES_ASSIGN.convertToWire(c);
    }
    if (command instanceof final NPUCommandRolesRevoke c) {
      return COMMAND_ROLES_REVOKE.convertToWire(c);
    }
    if (command instanceof final NPUCommandRolesGet c) {
      return COMMAND_ROLES_GET.convertToWire(c);
    }

    if (command instanceof final NPUCommandAgentLabelPut c) {
      return COMMAND_AGENT_LABEL_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelGet c) {
      return COMMAND_AGENT_LABEL_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelSearchBegin c) {
      return COMMAND_AGENT_LABEL_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelSearchNext c) {
      return COMMAND_AGENT_LABEL_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelSearchPrevious c) {
      return COMMAND_AGENT_LABEL_SEARCH_PREVIOUS.convertToWire(c);
    }
    if (command instanceof final NPUCommandAgentLabelDelete c) {
      return COMMAND_AGENT_LABEL_DELETE.convertToWire(c);
    }

    if (command instanceof final NPUCommandToolExecutionDescriptionPut c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionValidate c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionGet c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_GET.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionSearchBegin c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionSearchNext c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT.convertToWire(c);
    }
    if (command instanceof final NPUCommandToolExecutionDescriptionSearchPrevious c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS.convertToWire(c);
    }

    throw new IllegalStateException("Unrecognized command: " + command);
  }

  @Override
  public NPUMessageType convertFromWire(
    final ProtocolNPUv1Type message)
  {
    if (message instanceof final NPU1CommandLogin c) {
      return COMMAND_LOGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandDisconnect c) {
      return COMMAND_DISCONNECT.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandRolesAssign c) {
      return COMMAND_ROLES_ASSIGN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRolesRevoke c) {
      return COMMAND_ROLES_REVOKE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRolesGet c) {
      return COMMAND_ROLES_GET.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandRepositoryPut c) {
      return COMMAND_REPOSITORY_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositoryGet c) {
      return COMMAND_REPOSITORY_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositorySearchBegin c) {
      return COMMAND_REPOSITORY_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositorySearchNext c) {
      return COMMAND_REPOSITORY_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandRepositorySearchPrevious c) {
      return COMMAND_REPOSITORY_SEARCH_PREVIOUS.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandAgentLabelPut c) {
      return COMMAND_AGENT_LABEL_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelGet c) {
      return COMMAND_AGENT_LABEL_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelSearchBegin c) {
      return COMMAND_AGENT_LABEL_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelSearchNext c) {
      return COMMAND_AGENT_LABEL_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelSearchPrevious c) {
      return COMMAND_AGENT_LABEL_SEARCH_PREVIOUS.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandAgentLabelDelete c) {
      return COMMAND_AGENT_LABEL_DELETE.convertFromWire(c);
    }

    if (message instanceof final NPU1CommandToolExecutionDescriptionPut c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_PUT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionValidate c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionGet c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_GET.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionSearchBegin c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_BEGIN.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionSearchNext c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_NEXT.convertFromWire(c);
    }
    if (message instanceof final NPU1CommandToolExecutionDescriptionSearchPrevious c) {
      return COMMAND_TOOL_EXECUTION_DESCRIPTION_SEARCH_PREVIOUS.convertFromWire(c);
    }

    if (message instanceof final NPU1ResponseError r) {
      return RESPONSE_ERROR.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseOK r) {
      return RESPONSE_OK.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseRolesGet r) {
      return RESPONSE_ROLES_GET.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseRepositoryGet r) {
      return RESPONSE_REPOSITORY_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseRepositorySearch r) {
      return RESPONSE_REPOSITORY_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseAgentLabelGet r) {
      return RESPONSE_AGENT_LABEL_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseAgentLabelSearch r) {
      return RESPONSE_AGENT_LABEL_SEARCH.convertFromWire(r);
    }

    if (message instanceof final NPU1ResponseToolExecutionDescriptionValidate r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_VALIDATE.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseToolExecutionDescriptionGet r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_GET.convertFromWire(r);
    }
    if (message instanceof final NPU1ResponseToolExecutionDescriptionSearch r) {
      return RESPONSE_TOOL_EXECUTION_DESCRIPTION_SEARCH.convertFromWire(r);
    }

    throw new IllegalStateException("Unrecognized message: " + message);
  }
}
