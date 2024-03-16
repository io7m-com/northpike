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

package com.io7m.northpike.protocol.agent_console.cb;


import com.io7m.northpike.protocol.agent_console.NPACCommandAgentCreate;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentDelete;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentList;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentServerAssign;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentWorkExecPut;
import com.io7m.northpike.protocol.agent_console.NPACCommandDisconnect;
import com.io7m.northpike.protocol.agent_console.NPACCommandLogin;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerDelete;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerList;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACCommandType;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecSupported;
import com.io7m.northpike.protocol.agent_console.NPACEventType;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgentList;
import com.io7m.northpike.protocol.agent_console.NPACResponseError;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.protocol.agent_console.NPACResponseServer;
import com.io7m.northpike.protocol.agent_console.NPACResponseServerList;
import com.io7m.northpike.protocol.agent_console.NPACResponseType;
import com.io7m.northpike.protocol.agent_console.NPACResponseWorkExecGet;
import com.io7m.northpike.protocol.agent_console.NPACResponseWorkExecSupported;
import com.io7m.northpike.protocol.api.NPProtocolException;
import com.io7m.northpike.protocol.api.NPProtocolMessageValidatorType;

import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandAgentCreate.COMMAND_AGENT_CREATE;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandAgentDelete.COMMAND_AGENT_DELETE;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandAgentGet.COMMAND_AGENT_GET;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandAgentList.COMMAND_AGENT_LIST;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandAgentServerAssign.COMMAND_AGENT_SERVER_ASSIGN;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandAgentWorkExecPut.COMMAND_AGENT_WORK_EXEC_PUT;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandDisconnect.COMMAND_DISCONNECT;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandLogin.COMMAND_LOGIN;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandServerDelete.COMMAND_SERVER_DELETE;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandServerGet.COMMAND_SERVER_GET;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandServerList.COMMAND_SERVER_LIST;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandServerPut.COMMAND_SERVER_PUT;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandWorkExecGet.COMMAND_WORK_EXEC_GET;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVCommandWorkExecSupported.COMMAND_WORK_EXEC_SUPPORTED;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseAgent.RESPONSE_AGENT;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseAgentList.RESPONSE_AGENT_LIST;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseError.RESPONSE_ERROR;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseOK.RESPONSE_OK;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseServer.RESPONSE_SERVER;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseServerList.RESPONSE_SERVER_LIST;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseWorkExecGet.RESPONSE_WORK_EXEC_GET;
import static com.io7m.northpike.protocol.agent_console.cb.internal.NPACVResponseWorkExecSupported.RESPONSE_WORK_EXEC_SUPPORTED;

/**
 * Functions to translate between the core command set and the Console
 * Cedarbridge encoding command set.
 */

public final class NPACValidation
  implements NPProtocolMessageValidatorType<NPACMessageType, ProtocolNPACType>
{
  /**
   * Functions to translate between the core command set and the Console
   * Cedarbridge encoding command set.
   */

  public NPACValidation()
  {

  }

  @Override
  public ProtocolNPACType convertToWire(
    final NPACMessageType message)
    throws NPProtocolException
  {
    return switch (message) {
      case final NPACCommandType<?> m -> {
        yield switch (m) {
          case final NPACCommandLogin c -> {
            yield COMMAND_LOGIN.convertToWire(c);
          }
          case final NPACCommandDisconnect c -> {
            yield COMMAND_DISCONNECT.convertToWire(c);
          }
          case final NPACCommandServerDelete c -> {
            yield COMMAND_SERVER_DELETE.convertToWire(c);
          }
          case final NPACCommandServerGet c -> {
            yield COMMAND_SERVER_GET.convertToWire(c);
          }
          case final NPACCommandServerList c -> {
            yield COMMAND_SERVER_LIST.convertToWire(c);
          }
          case final NPACCommandServerPut c -> {
            yield COMMAND_SERVER_PUT.convertToWire(c);
          }
          case final NPACCommandWorkExecGet c -> {
            yield COMMAND_WORK_EXEC_GET.convertToWire(c);
          }
          case final NPACCommandAgentWorkExecPut c -> {
            yield COMMAND_AGENT_WORK_EXEC_PUT.convertToWire(c);
          }
          case final NPACCommandAgentDelete c -> {
            yield COMMAND_AGENT_DELETE.convertToWire(c);
          }
          case final NPACCommandAgentCreate c -> {
            yield COMMAND_AGENT_CREATE.convertToWire(c);
          }
          case final NPACCommandAgentGet c -> {
            yield COMMAND_AGENT_GET.convertToWire(c);
          }
          case final NPACCommandAgentList c -> {
            yield COMMAND_AGENT_LIST.convertToWire(c);
          }
          case final NPACCommandAgentServerAssign c -> {
            yield COMMAND_AGENT_SERVER_ASSIGN.convertToWire(c);
          }
          case final NPACCommandWorkExecSupported c -> {
            yield COMMAND_WORK_EXEC_SUPPORTED.convertToWire(c);
          }
        };
      }
      case final NPACEventType m -> {
        throw new IllegalStateException("Unexpected value: " + m);
      }
      case final NPACResponseType m -> {
        yield switch (m) {
          case final NPACResponseError r -> {
            yield RESPONSE_ERROR.convertToWire(r);
          }
          case final NPACResponseOK r -> {
            yield RESPONSE_OK.convertToWire(r);
          }
          case final NPACResponseServer r -> {
            yield RESPONSE_SERVER.convertToWire(r);
          }
          case final NPACResponseServerList r -> {
            yield RESPONSE_SERVER_LIST.convertToWire(r);
          }
          case final NPACResponseAgent r -> {
            yield RESPONSE_AGENT.convertToWire(r);
          }
          case final NPACResponseAgentList r -> {
            yield RESPONSE_AGENT_LIST.convertToWire(r);
          }
          case final NPACResponseWorkExecGet r -> {
            yield RESPONSE_WORK_EXEC_GET.convertToWire(r);
          }
          case final NPACResponseWorkExecSupported r -> {
            yield RESPONSE_WORK_EXEC_SUPPORTED.convertToWire(r);
          }
        };
      }
    };
  }

  @Override
  public NPACMessageType convertFromWire(
    final ProtocolNPACType message)
    throws NPProtocolException
  {
    return switch (message) {
      case final ProtocolNPACv1Type v1 -> {
        yield switch (v1) {
          case final NPAC1CommandLogin m -> {
            yield COMMAND_LOGIN.convertFromWire(m);
          }
          case final NPAC1CommandDisconnect m -> {
            yield COMMAND_DISCONNECT.convertFromWire(m);
          }
          case final NPAC1ResponseError m -> {
            yield RESPONSE_ERROR.convertFromWire(m);
          }
          case final NPAC1ResponseOK m -> {
            yield RESPONSE_OK.convertFromWire(m);
          }
          case final NPAC1CommandServerDelete m -> {
            yield COMMAND_SERVER_DELETE.convertFromWire(m);
          }
          case final NPAC1CommandServerGet m -> {
            yield COMMAND_SERVER_GET.convertFromWire(m);
          }
          case final NPAC1CommandServerList m -> {
            yield COMMAND_SERVER_LIST.convertFromWire(m);
          }
          case final NPAC1CommandServerPut m -> {
            yield COMMAND_SERVER_PUT.convertFromWire(m);
          }
          case final NPAC1ResponseServer m -> {
            yield RESPONSE_SERVER.convertFromWire(m);
          }
          case final NPAC1ResponseServerList m -> {
            yield RESPONSE_SERVER_LIST.convertFromWire(m);
          }
          case final NPAC1CommandWorkExecGet m -> {
            yield COMMAND_WORK_EXEC_GET.convertFromWire(m);
          }
          case final NPAC1CommandAgentCreate m -> {
            yield COMMAND_AGENT_CREATE.convertFromWire(m);
          }
          case final NPAC1CommandAgentDelete m -> {
            yield COMMAND_AGENT_DELETE.convertFromWire(m);
          }
          case final NPAC1CommandAgentGet m -> {
            yield COMMAND_AGENT_GET.convertFromWire(m);
          }
          case final NPAC1CommandAgentList m -> {
            yield COMMAND_AGENT_LIST.convertFromWire(m);
          }
          case final NPAC1ResponseAgent m -> {
            yield RESPONSE_AGENT.convertFromWire(m);
          }
          case final NPAC1ResponseAgentList m -> {
            yield RESPONSE_AGENT_LIST.convertFromWire(m);
          }
          case final NPAC1CommandAgentServerAssign m -> {
            yield COMMAND_AGENT_SERVER_ASSIGN.convertFromWire(m);
          }
          case final NPAC1CommandAgentWorkExecPut m -> {
            yield COMMAND_AGENT_WORK_EXEC_PUT.convertFromWire(m);
          }
          case final NPAC1CommandWorkExecSupported m -> {
            yield COMMAND_WORK_EXEC_SUPPORTED.convertFromWire(m);
          }
          case final NPAC1ResponseWorkExecGet m -> {
            yield RESPONSE_WORK_EXEC_GET.convertFromWire(m);
          }
          case final NPAC1ResponseWorkExecSupported m -> {
            yield RESPONSE_WORK_EXEC_SUPPORTED.convertFromWire(m);
          }
        };
      }
    };
  }
}
