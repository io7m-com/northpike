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


package com.io7m.northpike.agent.internal.console;


import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorFactoryType;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorSummary;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent_console.NPACCommandAgentWorkExecPut;
import com.io7m.northpike.protocol.agent_console.NPACCommandWorkExecSupported;
import com.io7m.northpike.protocol.agent_console.NPACResponseWorkExecSupported;

import java.util.ArrayList;
import java.util.List;
import java.util.UUID;

/**
 * @see NPACCommandWorkExecSupported
 */

public final class NPACCmdWorkExecSupported
  extends NPACCmdAbstract<NPACResponseWorkExecSupported, NPACCommandWorkExecSupported>
{
  /**
   * @see NPACCommandAgentWorkExecPut
   */

  public NPACCmdWorkExecSupported()
  {
    super(NPACCommandWorkExecSupported.class);
  }

  @Override
  public NPACResponseWorkExecSupported execute(
    final NPACCommandContextType context,
    final NPACCommandWorkExecSupported command)
    throws NPException
  {
    context.onAuthenticationRequire();

    final var services =
      context.services();
    final var workExecutors =
      services.optionalServices(NPAWorkExecutorFactoryType.class);
    final var summaries =
      new ArrayList<NPAWorkExecutorSummary>();

    for (final var workExecutor : workExecutors) {
      summaries.add(
        new NPAWorkExecutorSummary(
          workExecutor.name(),
          workExecutor.description(),
          workExecutor.properties()
        )
      );
    }

    return new NPACResponseWorkExecSupported(
      UUID.randomUUID(),
      command.messageID(),
      List.copyOf(summaries)
    );
  }
}
