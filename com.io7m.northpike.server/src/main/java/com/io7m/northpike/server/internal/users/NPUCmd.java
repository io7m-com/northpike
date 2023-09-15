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


package com.io7m.northpike.server.internal.users;

import com.io7m.northpike.model.NPException;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelDelete;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelGet;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelPut;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAgentLabelSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentGet;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentPut;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandAssignmentSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandDisconnect;
import com.io7m.northpike.protocol.user.NPUCommandLogin;
import com.io7m.northpike.protocol.user.NPUCommandPlanGet;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchBegin;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchNext;
import com.io7m.northpike.protocol.user.NPUCommandPlanSearchPrevious;
import com.io7m.northpike.protocol.user.NPUCommandPlanValidate;
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
import com.io7m.northpike.protocol.user.NPUMessageType;
import com.io7m.northpike.protocol.user.NPUResponseType;

import static com.io7m.northpike.model.NPStandardErrorCodes.errorProtocol;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_PROTOCOL;

/**
 * @see NPUMessageType
 */

public final class NPUCmd
{
  /**
   * @see NPUMessageType
   */

  public NPUCmd()
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

  public NPUResponseType execute(
    final NPUserCommandContextType context,
    final NPUMessageType message)
    throws NPException
  {
    if (message instanceof final NPUCommandType<?> command) {
      if (command instanceof final NPUCommandLogin c) {
        return new NPUCmdLogin().execute(context, c);
      }
      if (command instanceof final NPUCommandDisconnect c) {
        return new NPUCmdDisconnect().execute(context, c);
      }

      if (command instanceof final NPUCommandRepositoryPut c) {
        return new NPUCmdRepositoryPut().execute(context, c);
      }
      if (command instanceof final NPUCommandRepositoryGet c) {
        return new NPUCmdRepositoryGet().execute(context, c);
      }
      if (command instanceof final NPUCommandRepositorySearchBegin c) {
        return new NPUCmdRepositorySearchBegin().execute(context, c);
      }
      if (command instanceof final NPUCommandRepositorySearchNext c) {
        return new NPUCmdRepositorySearchNext().execute(context, c);
      }
      if (command instanceof final NPUCommandRepositorySearchPrevious c) {
        return new NPUCmdRepositorySearchPrevious().execute(context, c);
      }

      if (command instanceof final NPUCommandRolesAssign c) {
        return new NPUCmdRolesAssign().execute(context, c);
      }
      if (command instanceof final NPUCommandRolesRevoke c) {
        return new NPUCmdRolesRevoke().execute(context, c);
      }
      if (command instanceof final NPUCommandRolesGet c) {
        return new NPUCmdRolesGet().execute(context, c);
      }

      if (command instanceof final NPUCommandAgentLabelPut c) {
        return new NPUCmdAgentLabelPut().execute(context, c);
      }
      if (command instanceof final NPUCommandAgentLabelGet c) {
        return new NPUCmdAgentLabelGet().execute(context, c);
      }
      if (command instanceof final NPUCommandAgentLabelSearchBegin c) {
        return new NPUCmdAgentLabelSearchBegin().execute(context, c);
      }
      if (command instanceof final NPUCommandAgentLabelSearchNext c) {
        return new NPUCmdAgentLabelSearchNext().execute(context, c);
      }
      if (command instanceof final NPUCommandAgentLabelSearchPrevious c) {
        return new NPUCmdAgentLabelSearchPrevious().execute(context, c);
      }
      if (command instanceof final NPUCommandAgentLabelDelete c) {
        return new NPUCmdAgentLabelDelete().execute(context, c);
      }

      if (command instanceof final NPUCommandToolExecutionDescriptionValidate c) {
        return new NPUCmdToolExecutionDescriptionValidate().execute(context, c);
      }
      if (command instanceof final NPUCommandToolExecutionDescriptionPut c) {
        return new NPUCmdToolExecutionDescriptionPut().execute(context, c);
      }
      if (command instanceof final NPUCommandToolExecutionDescriptionGet c) {
        return new NPUCmdToolExecutionDescriptionGet().execute(context, c);
      }
      if (command instanceof final NPUCommandToolExecutionDescriptionSearchBegin c) {
        return new NPUCmdToolExecutionDescriptionSearchBegin()
          .execute(context, c);
      }
      if (command instanceof final NPUCommandToolExecutionDescriptionSearchNext c) {
        return new NPUCmdToolExecutionDescriptionSearchNext()
          .execute(context, c);
      }
      if (command instanceof final NPUCommandToolExecutionDescriptionSearchPrevious c) {
        return new NPUCmdToolExecutionDescriptionSearchPrevious()
          .execute(context, c);
      }

      if (command instanceof final NPUCommandPlanValidate c) {
        return new NPUCmdPlanValidate().execute(context, c);
      }
      if (command instanceof final NPUCommandPlanPut c) {
        return new NPUCmdPlanPut().execute(context, c);
      }
      if (command instanceof final NPUCommandPlanGet c) {
        return new NPUCmdPlanGet().execute(context, c);
      }
      if (command instanceof final NPUCommandPlanSearchBegin c) {
        return new NPUCmdPlanSearchBegin().execute(context, c);
      }
      if (command instanceof final NPUCommandPlanSearchNext c) {
        return new NPUCmdPlanSearchNext().execute(context, c);
      }
      if (command instanceof final NPUCommandPlanSearchPrevious c) {
        return new NPUCmdPlanSearchPrevious().execute(context, c);
      }

      if (command instanceof final NPUCommandAssignmentPut c) {
        return new NPUCmdAssignmentPut().execute(context, c);
      }
      if (command instanceof final NPUCommandAssignmentGet c) {
        return new NPUCmdAssignmentGet().execute(context, c);
      }
      if (command instanceof final NPUCommandAssignmentSearchBegin c) {
        return new NPUCmdAssignmentSearchBegin().execute(context, c);
      }
      if (command instanceof final NPUCommandAssignmentSearchNext c) {
        return new NPUCmdAssignmentSearchNext().execute(context, c);
      }
      if (command instanceof final NPUCommandAssignmentSearchPrevious c) {
        return new NPUCmdAssignmentSearchPrevious().execute(context, c);
      }
    }
    throw context.fail(ERROR_PROTOCOL, errorProtocol());
  }
}
