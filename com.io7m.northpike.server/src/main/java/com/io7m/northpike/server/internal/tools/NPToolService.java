/*
 * Copyright © 2024 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.northpike.server.internal.tools;

import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesToolsType.PutExecutionDescriptionType;
import com.io7m.northpike.database.api.NPDatabaseRole;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPToolExecutionDescription;
import com.io7m.northpike.model.NPToolExecutionIdentifier;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.toolexec.api.NPTEvaluationLanguageProviderType;
import com.io7m.northpike.toolexec.lines.NPTLinesLanguageProvider;
import com.io7m.northpike.tools.api.NPToolFactoryType;
import io.opentelemetry.api.trace.SpanKind;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;

/**
 * The tool service.
 */

public final class NPToolService
  implements NPToolServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPToolService.class);

  private static final NPTEvaluationLanguageProviderType LINES_PROVIDER =
    new NPTLinesLanguageProvider();

  private final NPTelemetryServiceType telemetry;
  private final NPDatabaseType database;
  private final Collection<? extends NPToolFactoryType> toolFactories;

  private NPToolService(
    final NPTelemetryServiceType inTelemetry,
    final NPDatabaseType inDatabase,
    final Collection<? extends NPToolFactoryType> inToolFactories)
  {
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.toolFactories =
      Objects.requireNonNull(inToolFactories, "toolFactories");
  }

  /**
   * Create a tool service.
   *
   * @param telemetry     The telemetry
   * @param database      The database
   * @param toolFactories The tool factories
   *
   * @return A tool service
   */

  public static NPToolServiceType create(
    final NPTelemetryServiceType telemetry,
    final NPDatabaseType database,
    final Collection<? extends NPToolFactoryType> toolFactories)
  {
    return new NPToolService(telemetry, database, toolFactories);
  }

  @Override
  public CompletableFuture<Void> start()
  {
    final var future = new CompletableFuture<Void>();
    Thread.startVirtualThread(() -> {
      try {
        future.complete(this.doStart());
      } catch (final Throwable e) {
        future.completeExceptionally(e);
      }
    });
    return future;
  }

  private Void doStart()
    throws Exception
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("ToolServiceStartup")
        .setSpanKind(SpanKind.INTERNAL)
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      try (var connection = this.database.openConnection(NPDatabaseRole.NORTHPIKE)) {
        try (var transaction = connection.openTransaction()) {
          transaction.setOwner(new NPAuditOwnerType.Server());

          try {
            this.updateTools(transaction);
          } catch (final Exception e) {
            LOG.error("", e);
            span.recordException(e);
          }

          transaction.commit();
        }
      }
      return null;
    } catch (final Exception e) {
      LOG.error("", e);
      span.recordException(e);
      throw e;
    } finally {
      span.end();
    }
  }

  private void updateTools(
    final NPDatabaseTransactionType transaction)
    throws NPDatabaseException
  {
    final var toolDescriptions =
      new ArrayList<NPToolExecutionDescription>();

    for (final var tool : this.toolFactories) {
      final var executions = tool.defaultExecutions();

      for (final var entry : executions.entrySet()) {
        final var execName =
          entry.getKey();
        final var execLines =
          entry.getValue();

        toolDescriptions.add(
          new NPToolExecutionDescription(
            new NPToolExecutionIdentifier(execName, 0L),
            tool.toolName(),
            "Built-in %s execution".formatted(execName),
            LINES_PROVIDER.languageSupported(),
            String.join("\n", execLines)
          )
        );
      }
    }

    final var toolPut = transaction.queries(PutExecutionDescriptionType.class);
    for (final var toolDescription : toolDescriptions) {
      toolPut.execute(toolDescription);
    }
  }

  @Override
  public String description()
  {
    return "Tool service.";
  }

  @Override
  public void close()
    throws Exception
  {

  }
}
