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


package com.io7m.northpike.tests.arbitraries.protocol.agent_console;

import com.io7m.northpike.protocol.agent_console.NPACCommandAgentCreate;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentDelete;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentList;
import com.io7m.northpike.protocol.agent_console.NPACCommandDisconnect;
import com.io7m.northpike.protocol.agent_console.NPACCommandLogin;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerDelete;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerList;
import com.io7m.northpike.protocol.agent_console.NPACCommandServerPut;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecGet;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecPut;
import com.io7m.northpike.protocol.agent_console.NPACMessageType;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgent;
import com.io7m.northpike.protocol.agent_console.NPACResponseAgentList;
import com.io7m.northpike.protocol.agent_console.NPACResponseError;
import com.io7m.northpike.protocol.agent_console.NPACResponseOK;
import com.io7m.northpike.protocol.agent_console.NPACResponseServer;
import com.io7m.northpike.protocol.agent_console.NPACResponseServerList;
import com.io7m.northpike.protocol.agent_console.NPACResponseWorkExec;
import com.io7m.northpike.tests.arbitraries.NPArbAbstract;
import net.jqwik.api.Arbitraries;

import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class NPArbACMessage extends NPArbAbstract<NPACMessageType>
{
  public NPArbACMessage()
  {
    super(
      NPACMessageType.class,
      () -> {
        return Arbitraries.oneOf(
          Stream.of(
              NPACCommandAgentCreate.class,
              NPACCommandAgentDelete.class,
              NPACCommandAgentGet.class,
              NPACCommandAgentList.class,
              NPACCommandDisconnect.class,
              NPACCommandLogin.class,
              NPACCommandServerDelete.class,
              NPACCommandServerGet.class,
              NPACCommandServerList.class,
              NPACCommandServerPut.class,
              NPACCommandWorkExecGet.class,
              NPACCommandWorkExecPut.class,
              NPACResponseAgent.class,
              NPACResponseAgentList.class,
              NPACResponseError.class,
              NPACResponseOK.class,
              NPACResponseServer.class,
              NPACResponseServerList.class,
              NPACResponseWorkExec.class
            ).map(Arbitraries::defaultFor)
            .collect(Collectors.toUnmodifiableList())
        );
      }
    );
  }
}
