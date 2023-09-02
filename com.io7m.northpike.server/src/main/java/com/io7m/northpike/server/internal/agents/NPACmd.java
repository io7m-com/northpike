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


package com.io7m.northpike.server.internal.agents;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.agent.NPACommandCDisconnect;
import com.io7m.northpike.protocol.agent.NPACommandCEnvironmentInfo;
import com.io7m.northpike.protocol.agent.NPACommandCLogin;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemFailed;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemOutput;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemStarted;
import com.io7m.northpike.protocol.agent.NPACommandCWorkItemSucceeded;
import com.io7m.northpike.protocol.agent.NPACommandType;
import com.io7m.northpike.protocol.agent.NPAMessageType;
import com.io7m.northpike.protocol.agent.NPAResponseType;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;

/**
 * @see NPAMessageType
 */

public final class NPACmd
{
  /**
   * @see NPAMessageType
   */

  public NPACmd()
  {

  }

  /**
   * Execute a message.
   *
   * @param context The command context
   * @param message The message
   *
   * @return The result of executing the message
   *
   * @throws NPException On errors
   */

  public NPAResponseType execute(
    final NPAgentCommandContextType context,
    final NPAMessageType message)
    throws NPException
  {
    if (message instanceof final NPACommandType<?> command) {
      if (command instanceof final NPACommandCEnvironmentInfo c) {
        return new NPACmdEnvironmentInfo().execute(context, c);
      }
      if (command instanceof final NPACommandCLogin c) {
        return new NPACmdLogin().execute(context, c);
      }
      if (command instanceof final NPACommandCDisconnect c) {
        return new NPACmdDisconnect().execute(context, c);
      }
      if (command instanceof final NPACommandCWorkItemStarted c) {
        return new NPACmdWorkItemStarted().execute(context, c);
      }
      if (command instanceof final NPACommandCWorkItemOutput c) {
        return new NPACmdWorkItemOutput().execute(context, c);
      }
      if (command instanceof final NPACommandCWorkItemSucceeded c) {
        return new NPACmdWorkItemSucceeded().execute(context, c);
      }
      if (command instanceof final NPACommandCWorkItemFailed c) {
        return new NPACmdWorkItemFailed().execute(context, c);
      }
    }

    throw context.fail(ERROR_PROTOCOL, errorProtocol());
  }
}
