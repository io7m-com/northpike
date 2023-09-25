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

import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.PutExecutionDescriptionType;
import com.io7m.northpike.model.NPAuditUserOrAgentType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.protocol.user.NPUCommandToolExecutionDescriptionPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.toolexec.NPTXCompilationResultType;
import com.io7m.northpike.toolexec.NPTXCompilerConfiguration;
import com.io7m.northpike.toolexec.NPTXCompilerFactoryType;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;
import com.io7m.northpike.toolexec.model.NPTXPlanVariables;

import java.util.List;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_COMPILATION_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.FORMAT;
import static com.io7m.northpike.strings.NPStringConstants.SUGGEST_COMPILATION_FAILED;

/**
 * @see NPUCommandToolExecutionDescriptionPut
 */

public final class NPUCmdToolExecutionDescriptionPut
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandToolExecutionDescriptionPut>
{
  /**
   * @see NPUCommandToolExecutionDescriptionPut
   */

  public NPUCmdToolExecutionDescriptionPut()
  {
    super(NPUCommandToolExecutionDescriptionPut.class);
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandToolExecutionDescriptionPut command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.TOOLS.object(),
      NPSecAction.WRITE.action()
    );

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
        NPTXPlanVariables.ofList(List.of()),
        command.description().format(),
        command.description().text()
      );

    if (result instanceof final NPTXCompilationResultType.Failure f) {
      throw context.failWithRemediation(
        ERROR_COMPILATION_FAILED,
        NPStandardErrorCodes.errorCompilationFailed(),
        SUGGEST_COMPILATION_FAILED
      );
    }

    if (result instanceof NPTXCompilationResultType.Success) {
      try (var connection = context.databaseConnection()) {
        try (var transaction = connection.openTransaction()) {
          transaction.setOwner(new NPAuditUserOrAgentType.User(user.userId()));
          transaction.queries(PutExecutionDescriptionType.class)
            .execute(command.description());
          transaction.commit();
          return NPUResponseOK.createCorrelated(command);
        }
      }
    }

    throw new IllegalStateException(
      "Unrecognized result: %s".formatted(result)
    );
  }
}
