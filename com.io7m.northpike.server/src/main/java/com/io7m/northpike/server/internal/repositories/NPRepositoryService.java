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


package com.io7m.northpike.server.internal.repositories;

import com.io7m.jmulticlose.core.CloseableCollectionType;
import com.io7m.northpike.database.api.NPDatabaseException;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsGetMostRecentlyReceivedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.CommitsPutType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryException;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryFactoryType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.telemetry.api.NPTelemetryServiceType.recordSpanException;

/**
 * The repository service.
 */

public final class NPRepositoryService
  implements NPRepositoryServiceType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(NPRepositoryService.class);

  private final AtomicBoolean closed;
  private final CompletableFuture<Void> future;
  private final RPServiceDirectoryType services;
  private final CloseableCollectionType<NPServerException> resources;
  private final ExecutorService mainExecutor;
  private final NPEventServiceType events;
  private final NPDatabaseType database;
  private final LinkedBlockingQueue<NPRepositoryCommandType> commands;
  private final NPTelemetryServiceType telemetry;
  private final List<? extends NPSCMRepositoryFactoryType> scmFactories;
  private final NPStrings strings;
  private final HashMap<UUID, NPSCMRepositoryType> repositories;
  private final Path dataDirectory;

  private NPRepositoryService(
    final RPServiceDirectoryType inServices,
    final CloseableCollectionType<NPServerException> inResources,
    final ExecutorService inMainExecutor,
    final NPEventServiceType inEvents,
    final NPDatabaseType inDatabase,
    final NPTelemetryServiceType inTelemetry,
    final List<? extends NPSCMRepositoryFactoryType> inScmFactories,
    final NPStrings inStrings,
    final Path inDataDirectory)
  {
    this.services =
      Objects.requireNonNull(inServices, "services");
    this.resources =
      Objects.requireNonNull(inResources, "resources");
    this.mainExecutor =
      Objects.requireNonNull(inMainExecutor, "mainExecutor");
    this.events =
      Objects.requireNonNull(inEvents, "events");
    this.database =
      Objects.requireNonNull(inDatabase, "database");
    this.telemetry =
      Objects.requireNonNull(inTelemetry, "telemetry");
    this.scmFactories =
      Objects.requireNonNull(inScmFactories, "scmFactories");
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.dataDirectory =
      Objects.requireNonNull(inDataDirectory, "dataDirectory");
    this.closed =
      new AtomicBoolean(true);
    this.future =
      new CompletableFuture<>();
    this.commands =
      new LinkedBlockingQueue<>();
    this.repositories =
      new HashMap<UUID, NPSCMRepositoryType>();
  }

  /**
   * Create a repository service.
   *
   * @param services The service directory
   *
   * @return The service
   */

  public static NPRepositoryServiceType create(
    final RPServiceDirectoryType services)
  {
    Objects.requireNonNull(services, "services");

    final var events =
      services.requireService(NPEventServiceType.class);
    final var telemetry =
      services.requireService(NPTelemetryServiceType.class);
    final var database =
      services.requireService(NPDatabaseType.class);
    final var scmFactories =
      services.optionalServices(NPSCMRepositoryFactoryType.class);
    final var strings =
      services.requireService(NPStrings.class);
    final var configuration =
      services.requireService(NPConfigurationServiceType.class)
        .configuration();

    final var resources =
      NPServerResources.createResources();

    final var mainExecutor =
      Executors.newSingleThreadExecutor(runnable -> {
        final var thread = new Thread(runnable);
        thread.setName(
          "com.io7m.server.repository.service[%d]"
            .formatted(Long.valueOf(thread.getId()))
        );
        return thread;
      });

    resources.add(mainExecutor::shutdown);

    return new NPRepositoryService(
      services,
      resources,
      mainExecutor,
      events,
      database,
      telemetry,
      scmFactories,
      strings,
      configuration.directories().repositoryDirectory()
    );
  }

  @Override
  public CompletableFuture<Void> start()
  {
    if (this.closed.compareAndSet(true, false)) {
      this.mainExecutor.execute(this::run);
    }
    return this.future;
  }

  @Override
  public CompletableFuture<Void> check()
  {
    final var command = new CheckAll(new CompletableFuture<>());
    this.commands.add(command);
    return command.future;
  }

  private void run()
  {
    LOG.info("Starting Repository service");

    this.events.emit(new NPRepositoryServiceStarted());
    this.future.complete(null);

    while (!this.closed.get()) {
      NPRepositoryCommandType command = null;
      try {
        command = this.commands.poll(1L, TimeUnit.SECONDS);
      } catch (final InterruptedException e) {
        Thread.currentThread().interrupt();
      }
      if (command != null) {
        this.processCommandTimed(command);
      }
    }
  }

  private void processCommandTimed(
    final NPRepositoryCommandType command)
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder("Command")
        .setAttribute("Command", command.getClass().getSimpleName())
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      this.processCommand(command);
    } catch (final Throwable e) {
      recordSpanException(e);
      throw e;
    } finally {
      span.end();
    }
  }

  private void processCommand(
    final NPRepositoryCommandType command)
  {
    if (command instanceof final CheckAll check) {
      this.processCommandCheckAll(check);
      return;
    }
  }

  private void processCommandCheckAll(
    final CheckAll check)
  {
    try {
      final var repositoryDescriptions =
        this.repositoriesLoadDescriptions();

      this.repositoriesConfigureAll(repositoryDescriptions);
      this.repositoriesRemoveUnused(repositoryDescriptions);
      this.repositoriesUpdateAll();

    } catch (final Throwable e) {
      check.future.completeExceptionally(e);
    } finally {
      check.future.complete(null);
    }
  }

  private void repositoriesUpdateAll()
  {
    for (final var existing : this.repositories.values()) {
      this.repositoryUpdate(existing);
    }
  }

  private void repositoryUpdate(
    final NPSCMRepositoryType repository)
  {
    final var description = repository.description();

    final long commitCount;

    try {

      /*
       * Ask the repository for all commits received since the most recently
       * received commit recorded in the database. Then, push all those newer
       * commits to the database.
       */

      try (var connection = this.database.openConnection(NORTHPIKE)) {
        try (var transaction = connection.openTransaction()) {
          final var since =
            transaction.queries(CommitsGetMostRecentlyReceivedType.class)
              .execute(repository.description().id())
              .map(NPCommitSummary::timeReceived);

          final var commits =
            repository.commitsSinceTime(since);

          commitCount = Integer.toUnsignedLong(commits.commits().size());

          transaction.queries(CommitsPutType.class)
            .execute(new CommitsPutType.Parameters(
              commits.commits(),
              commits.commitGraph()
            ));

          transaction.commit();
        }
      }

    } catch (final NPException e) {
      recordSpanException(e);
      this.events.emit(new NPRepositoryUpdateFailed(
        description.id(),
        description.url(),
        description.provider(),
        e
      ));
      return;
    }

    this.events.emit(new NPRepositoryUpdated(
      description.id(),
      description.url(),
      description.provider(),
      commitCount
    ));
  }

  private void repositoriesRemoveUnused(
    final HashMap<UUID, NPRepositoryDescription> repositoryDescriptions)
  {
    final var remove = new HashSet<UUID>();

    for (final var existing : this.repositories.values()) {
      final var id = existing.description().id();
      if (!repositoryDescriptions.containsKey(id)) {
        remove.add(id);
      }
    }

    for (final var id : remove) {
      this.repositoryDelete(id);
    }
  }

  private void repositoryDelete(
    final UUID id)
  {
    final var existing =
      this.repositories.remove(id);
    final var description =
      existing.description();

    try {
      existing.close();
    } catch (final NPSCMRepositoryException e) {
      recordSpanException(e);
      this.events.emit(new NPRepositoryCloseFailed(
        description.id(),
        description.url(),
        description.provider(),
        e
      ));
      return;
    }

    this.events.emit(new NPRepositoryClosed(
      description.id(),
      description.url(),
      description.provider()
    ));
  }

  private void repositoriesConfigureAll(
    final HashMap<UUID, NPRepositoryDescription> repositoryDescriptions)
  {
    for (final var description : repositoryDescriptions.values()) {
      this.repositoryConfigure(description);
    }
  }

  private void repositoryConfigure(
    final NPRepositoryDescription description)
  {
    if (this.repositories.containsKey(description.id())) {
      return;
    }

    try {
      final var scmFactoryOpt =
        this.scmFactories.stream()
          .filter(factory -> Objects.equals(
            factory.providerName(),
            description.provider()))
          .findFirst();

      if (scmFactoryOpt.isEmpty()) {
        throw NPServerExceptions.errorUnsupportedSCMProvider(
          this.strings,
          description.id(),
          description.url(),
          description.provider()
        );
      }

      final var scmFactory =
        scmFactoryOpt.get();

      final NPSCMRepositoryType scm;
      try {
        scm = scmFactory.createRepository(
          this.services,
          this.dataDirectory,
          description
        );
      } catch (final NPSCMRepositoryException e) {
        throw NPServerExceptions.wrap(e);
      }

      this.resources.add(scm);
      this.repositories.put(description.id(), scm);
      this.events.emit(new NPRepositoryConfigured(
        description.id(),
        description.url(),
        description.provider()
      ));
    } catch (final NPServerException e) {
      recordSpanException(e);
      this.events.emit(new NPRepositoryConfigureFailed(
        description.id(),
        description.url(),
        description.provider(),
        e
      ));
    }
  }

  private HashMap<UUID, NPRepositoryDescription> repositoriesLoadDescriptions()
    throws NPDatabaseException
  {
    final var descriptions =
      new HashMap<UUID, NPRepositoryDescription>();

    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        final var list =
          transaction.queries(NPDatabaseQueriesRepositoriesType.ListType.class);
        final var paged =
          list.execute(NPDatabaseUnit.UNIT);
        final var pageInitial =
          paged.pageCurrent(transaction);

        final var pageCount = pageInitial.pageCount();
        for (int pageIndex = pageInitial.pageIndex(); pageIndex <= pageCount; ++pageIndex) {
          final var page =
            paged.pageCurrent(transaction);

          for (final var item : page.items()) {
            descriptions.put(item.id(), item);
          }
          paged.pageNext(transaction);
        }
      }
    }
    return descriptions;
  }

  @Override
  public boolean isClosed()
  {
    return this.closed.get();
  }

  @Override
  public String description()
  {
    return "The repository service.";
  }

  @Override
  public String toString()
  {
    return "[NPRepositoryService 0x%s]"
      .formatted(Integer.toUnsignedString(this.hashCode(), 16));
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.closed.compareAndSet(false, true)) {
      this.future.complete(null);
      this.resources.close();
    }
  }

  private sealed interface NPRepositoryCommandType
  {

  }

  record CheckAll(
    CompletableFuture<Void> future)
    implements NPRepositoryCommandType
  {

  }
}
