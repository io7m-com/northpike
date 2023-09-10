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
import com.io7m.northpike.plans.compiler.NPPlanCompilationResultType;
import com.io7m.northpike.plans.compiler.NPPlanCompilerConfiguration;
import com.io7m.northpike.plans.compiler.NPPlanCompilerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.protocol.user.NPUCommandPlanValidate;
import com.io7m.northpike.protocol.user.NPUResponsePlanValidate;
import com.io7m.northpike.strings.NPStrings;

import java.util.List;
import java.util.UUID;

/**
 * @see NPUCommandPlanValidate
 */

public final class NPUCmdPlanValidate
  implements NPUserCommandExecutorType<
  NPUResponsePlanValidate,
  NPUCommandPlanValidate>
{
  /**
   * @see NPUCommandPlanValidate
   */

  public NPUCmdPlanValidate()
  {

  }

  @Override
  public NPUResponsePlanValidate execute(
    final NPUserCommandContextType context,
    final NPUCommandPlanValidate command)
    throws NPException
  {
    context.onAuthenticationRequire();

    final var services =
      context.services();

    final var strings =
      services.requireService(NPStrings.class);
    final var parsersAvailable =
      services.optionalServices(NPPlanParserFactoryType.class);
    final var compilers =
      services.requireService(NPPlanCompilerFactoryType.class);

    final var compiler =
      compilers.create(
        new NPPlanCompilerConfiguration(
          strings,
          false,
          (List<NPPlanParserFactoryType>) parsersAvailable
        )
      );

    final var result =
      compiler.execute(
        command.plan().format(),
        command.plan().text()
      );

    if (result instanceof NPPlanCompilationResultType.Failure f) {
      return new NPUResponsePlanValidate(
        UUID.randomUUID(),
        command.messageID(),
        List.copyOf(f.messages())
      );
    }

    if (result instanceof NPPlanCompilationResultType.Success) {
      return new NPUResponsePlanValidate(
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
