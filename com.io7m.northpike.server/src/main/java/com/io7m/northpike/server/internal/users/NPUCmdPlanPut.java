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

import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType.PlanPutType.Parameters;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPStandardErrorCodes;
import com.io7m.northpike.model.security.NPSecAction;
import com.io7m.northpike.model.security.NPSecObject;
import com.io7m.northpike.plans.compiler.NPPlanCompilationResultType;
import com.io7m.northpike.plans.compiler.NPPlanCompilerConfiguration;
import com.io7m.northpike.plans.compiler.NPPlanCompilerFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanSerializerFactoryType;
import com.io7m.northpike.protocol.user.NPUCommandPlanPut;
import com.io7m.northpike.protocol.user.NPUResponseOK;
import com.io7m.northpike.server.internal.security.NPSecurity;
import com.io7m.northpike.strings.NPStrings;

import java.util.List;

import static com.io7m.northpike.strings.NPStringConstants.ERROR_COMPILATION_FAILED;
import static com.io7m.northpike.strings.NPStringConstants.SUGGEST_COMPILATION_FAILED;

/**
 * @see NPUCommandPlanPut
 */

public final class NPUCmdPlanPut
  extends NPUCmdAbstract<NPUResponseOK, NPUCommandPlanPut>
{
  /**
   * @see NPUCommandPlanPut
   */

  public NPUCmdPlanPut()
  {
    super(NPUCommandPlanPut.class);
  }

  @Override
  public NPUResponseOK execute(
    final NPUserCommandContextType context,
    final NPUCommandPlanPut command)
    throws NPException
  {
    final var user = context.onAuthenticationRequire();
    NPSecurity.check(
      user.userId(),
      user.subject(),
      NPSecObject.PLANS.object(),
      NPSecAction.WRITE.action()
    );

    final var services =
      context.services();

    final var strings =
      services.requireService(NPStrings.class);
    final var parsersAvailable =
      services.optionalServices(NPPlanParserFactoryType.class);
    final var compilers =
      services.requireService(NPPlanCompilerFactoryType.class);
    final var serializer =
      services.requireService(NPPlanSerializerFactoryType.class);

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

    if (result instanceof final NPPlanCompilationResultType.Failure f) {
      throw context.failWithRemediation(
        ERROR_COMPILATION_FAILED,
        NPStandardErrorCodes.errorCompilationFailed(),
        SUGGEST_COMPILATION_FAILED
      );
    }

    if (result instanceof final NPPlanCompilationResultType.Success s) {
      try (var transaction = context.transaction()) {
        transaction.setOwner(new NPAuditOwnerType.User(user.userId()));
        transaction.queries(NPDatabaseQueriesPlansType.PlanPutType.class)
          .execute(new Parameters(s.plan(), serializer));
        transaction.commit();
        return NPUResponseOK.createCorrelated(command);
      }
    }

    throw new IllegalStateException(
      "Unrecognized result: %s".formatted(result)
    );
  }
}
