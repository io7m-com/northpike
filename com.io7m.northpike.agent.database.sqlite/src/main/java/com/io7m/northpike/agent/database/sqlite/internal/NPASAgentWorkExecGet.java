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
import com.io7m.northpike.agent.database.api.NPAgentDatabaseQueriesAgentsType;
import com.io7m.northpike.agent.database.sqlite.internal.NPASQueryProviderType.Service;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecName;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorConfiguration;
import com.io7m.northpike.agent.workexec.api.NPAWorkExecutorContainerImage;
import com.io7m.northpike.model.agents.NPAgentLocalName;
import org.jooq.DSLContext;
import org.jooq.Record1;

import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Paths;
import java.util.Optional;
import java.util.Properties;

import static com.io7m.northpike.agent.database.sqlite.internal.tables.Agents.AGENTS;
import static com.io7m.northpike.strings.NPStringConstants.AGENT;

/**
 * Update an agent.
 */

public final class NPASAgentWorkExecGet
  extends NPASQAbstract<NPAgentLocalName, Optional<NPAWorkExecutorConfiguration>>
  implements NPAgentDatabaseQueriesAgentsType.AgentWorkExecGetType
{
  private static final Service<NPAgentLocalName, Optional<NPAWorkExecutorConfiguration>, AgentWorkExecGetType> SERVICE =
    new Service<>(AgentWorkExecGetType.class, NPASAgentWorkExecGet::new);

  /**
   * Construct a query.
   *
   * @param transaction The transaction
   */

  public NPASAgentWorkExecGet(
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

  private static Optional<NPAWorkExecutorConfiguration> mapRecordOpt(
    final Optional<Record1<String>> opt)
  {
    return opt.flatMap(NPASAgentWorkExecGet::mapRecord);

  }

  private static Optional<NPAWorkExecutorConfiguration> mapRecord(
    final Record1<String> r)
  {
    final var text = r.get(AGENTS.A_WORKEXEC);
    if (text == null) {
      return Optional.empty();
    }

    try (var reader = new StringReader(text)) {
      final var properties = new Properties();
      properties.load(reader);

      final var builder =
        NPAWorkExecutorConfiguration.builder();

      builder.setExecutorType(
        NPAWorkExecName.of(properties.getProperty("Type"))
      );
      builder.setTemporaryDirectory(Paths.get(
        properties.getProperty("TemporaryDirectory")
      ));
      builder.setWorkDirectory(Paths.get(
        properties.getProperty("WorkDirectory")
      ));

      Optional.ofNullable(
        properties.getProperty("WorkExecDistributionDirectory")
      ).ifPresent(x -> {
        builder.setWorkExecDistributionDirectory(Paths.get(x));
      });

      Optional.ofNullable(
        properties.getProperty("ContainerImage")
      ).ifPresent(x -> {
        final var image = new NPAWorkExecutorContainerImage(
          properties.getProperty("ContainerImage.Registry"),
          properties.getProperty("ContainerImage.Name"),
          properties.getProperty("ContainerImage.Tag"),
          Optional.ofNullable(properties.getProperty("ContainerImage.Hash"))
        );
        builder.setContainerImage(image);
      });

      return Optional.of(builder.build());
    } catch (final IOException e) {
      throw new IllegalStateException(e);
    }
  }

  @Override
  protected Optional<NPAWorkExecutorConfiguration> onExecute(
    final DSLContext context,
    final NPAgentLocalName name)
    throws NPAgentDatabaseException
  {
    this.setAttribute(AGENT, name.toString());

    final var query =
      context.select(AGENTS.A_WORKEXEC)
        .from(AGENTS)
        .where(AGENTS.A_NAME.eq(name.toString()));

    recordQuery(query);
    return mapRecordOpt(query.fetchOptional());
  }
}
