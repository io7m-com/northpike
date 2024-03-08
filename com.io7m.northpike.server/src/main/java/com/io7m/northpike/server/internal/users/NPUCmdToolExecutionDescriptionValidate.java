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
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionValidate;
import com.io7m.northpike.protocol.user.NPUResponseToolExecutionDescriptionValidate;
import com.io7m.northpike.toolexec.api.NPTEvaluationServiceType;
import com.io7m.northpike.toolexec.api.NPTException;
import com.io7m.seltzer.api.SStructuredError;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.UUID;

import static com.io7m.northpike.strings.NPStringConstants.FORMAT;

/**
 * @see NPUCommandToolExecutionDescriptionValidate
 */

public final class NPUCmdToolExecutionDescriptionValidate
  extends NPUCmdAbstract<
  NPUResponseToolExecutionDescriptionValidate,
  NPUCommandToolExecutionDescriptionValidate>
{
  /**
   * @see NPUCommandToolExecutionDescriptionValidate
   */

  public NPUCmdToolExecutionDescriptionValidate()
  {
    super(NPUCommandToolExecutionDescriptionValidate.class);
  }

  @Override
  public NPUResponseToolExecutionDescriptionValidate execute(
    final NPUserCommandContextType context,
    final NPUCommandToolExecutionDescriptionValidate command)
    throws NPException
  {
    context.onAuthenticationRequire();
    context.setAttribute(
      FORMAT,
      command.description().format().toString()
    );

    final var description = command.description();
    context.setAttribute(
      FORMAT,
      description.format().toString()
    );

    final var services =
      context.services();
    final var compiler =
      services.requireService(NPTEvaluationServiceType.class);

    final var evaluable =
      compiler.create(
        description.format(),
        List.of(),
        description.text()
      );

    try {
      evaluable.execute();
      return new NPUResponseToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        command.messageID(),
        List.of()
      );
    } catch (final NPTException e) {
      final var errors = new ArrayList<SStructuredError<String>>();
      errors.add(
        new SStructuredError<>(
          e.errorCode().id(),
          e.message(),
          e.attributes(),
          e.remediatingAction(),
          Optional.empty()
        )
      );
      errors.addAll(e.errors());

      return new NPUResponseToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        command.messageID(),
        List.copyOf(errors)
      );
    }
  }
}
