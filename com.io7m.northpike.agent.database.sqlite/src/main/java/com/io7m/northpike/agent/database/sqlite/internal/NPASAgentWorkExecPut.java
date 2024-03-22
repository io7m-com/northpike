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


package com.io7m.northpike.agent.database.sqlite.internal;

import com.io7m.northpike.agent.database.api.NPAgentDatabaseException;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentWorkExecPutType;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType.AgentWorkExecPutType.Parameters;
import com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.model.NPStandardErrorCodes;
import org.jooq.DSLContext;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.agent.database.api.NPAgentDatabaseUnit.UNIT;
import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;
import static com.io7m.northpike.strings.NPStringConstants.AGENT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;

/**
 * Update an agent.
 */

public final class NPASAgentWorkExecPut
  extends NPASQAbstract<Parameters, NPAgentDatabaseUnit>
  implements AgentWorkExecPutType
{
  private static final Service<Parameters, NPAgentDatabaseUnit, AgentWorkExecPutType> SERVICE =
    new Service<>(AgentWorkExecPutType.class, NPASAgentWorkExecPut::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentWorkExecPut(
    final NPASTransaction transaction)
  {
    super(transaction);
  }

  /**
   * @return A query provider
   */

  public static NPASQueryProviderType provider()
  {
    return () -> SERVICE;
  }

  private static String workExecToText(
    final Optional<NPAWorkExecutorConfiguration> configurationOpt)
  {
    if (configurationOpt.isEmpty()) {
      return null;
    }

    final var configuration =
      configurationOpt.get();

    try (var writer = new StringWriter()) {
      final var properties = new Properties();
      properties.setProperty(
        "Type",
        configuration.type().toString()
      );
      properties.setProperty(
        "WorkDirectory",
        configuration.workDirectory().toString()
      );
      properties.setProperty(
        "TemporaryDirectory",
        configuration.temporaryDirectory().toString()
      );

      configuration.workExecDistributionDirectory().ifPresent(p -> {
        properties.setProperty(
          "WorkExecDistributionDirectory",
          p.toString()
        );
      });

      configuration.containerImage().ifPresent(i -> {
        properties.setProperty("ContainerImage", "true");
        properties.setProperty("ContainerImage.Name", i.name());
        properties.setProperty("ContainerImage.Tag", i.tag());
        properties.setProperty("ContainerImage.Registry", i.registry());
        i.hash().ifPresent(h -> {
          properties.setProperty("ContainerImage.Hash", h);
        });
      });

      properties.store(writer, "");
      return writer.toString();
    } catch (final IOException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  protected NPAgentDatabaseUnit onExecute(
    final DSLContext context,
    final Parameters parameters)
    throws NPAgentDatabaseException
  {
    this.setAttribute(AGENT, parameters.agent().toString());

    final var query =
      context.update(AGENTS)
        .set(AGENTS.A_WORKEXEC, workExecToText(parameters.workExecutor()))
        .where(AGENTS.A_NAME.eq(parameters.agent().toString()));

    recordQuery(query);

    final var r = query.execute();
    if (r == 0) {
      throw new NPAgentDatabaseException(
        this.local(ERROR_NONEXISTENT),
        NPStandardErrorCodes.errorNonexistent(),
        this.attributes(),
        Optional.empty()
      );
    }
    return UNIT;
  }
}
