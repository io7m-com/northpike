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
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.NPTXCompilationResultType;
import com.io7m.northpike.toolexec.NPTXCompilerConfiguration;
import com.io7m.northpike.toolexec.NPTXCompilerFactoryType;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;

import java.util.List;
import java.util.UUID;

import static com.io7m.northpike.strings.NPStringConstants.FORMAT;

/**
 * @see NPUCommandToolExecutionDescriptionValidate
 */

public final class NPUCmdToolExecutionDescriptionValidate
  implements NPUserCommandExecutorType<
  NPUResponseToolExecutionDescriptionValidate,
  NPUCommandToolExecutionDescriptionValidate>
{
  /**
   * @see NPUCommandToolExecutionDescriptionValidate
   */

  public NPUCmdToolExecutionDescriptionValidate()
  {

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

    final var services =
      context.services();

    final var strings =
      services.requireService(NPStrings.class);
    final var parsersAvailable =
      services.optionalServices(NPTXParserFactoryType.class);
    final var compilers =
      services.requireService(NPTXCompilerFactoryType.class);

    final var compiler =
      compilers.create(
        new NPTXCompilerConfiguration(
          strings,
          false,
          (List<NPTXParserFactoryType>) parsersAvailable
        )
      );

    final var result =
      compiler.execute(
        NPTXPlanVariables.ofList(command.variables()),
        command.description().format(),
        command.description().text()
      );

    if (result instanceof NPTXCompilationResultType.Failure f) {
      return new NPUResponseToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        command.messageID(),
        List.copyOf(f.messages())
      );
    }

    if (result instanceof NPTXCompilationResultType.Success) {
      return new NPUResponseToolExecutionDescriptionValidate(
        UUID.randomUUID(),
        command.messageID(),
        List.of()
      );
    }

    throw new IllegalStateException(
      "Unrecognized result: %s".formatted(result)
    );
  }
}
