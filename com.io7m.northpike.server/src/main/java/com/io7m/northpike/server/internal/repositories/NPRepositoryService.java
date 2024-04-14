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
import com.io7m.northpike.database.api.NPDatabaseQueriesArchivesType.ArchivePutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitsGetMostRecentlyReceivedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryCommitsPutType.Parameters;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryGetType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryListType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyAssignType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPublicKeyIsAssignedType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType.RepositoryPutType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.database.api.NPDatabaseUnit;
import com.io7m.northpike.keys.NPSignatureKeyLookupType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPAuditOwnerType;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPException;
import com.io7m.northpike.model.NPFingerprint;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPRepositoryID;
import com.io7m.northpike.model.NPRepositorySigningPolicy;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryException;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryFactoryType;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.northpike.server.api.NPServerDirectoryConfiguration;
import com.io7m.northpike.server.api.NPServerException;
import com.io7m.northpike.server.internal.NPServerExceptions;
import com.io7m.northpike.server.internal.NPServerResources;
import com.io7m.northpike.server.internal.configuration.NPConfigurationServiceType;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import io.opentelemetry.api.trace.Span;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE_READ_ONLY;
import static com.io7m.northpike.model.NPStandardErrorCodes.errorNonexistent;
import static com.io7m.northpike.strings.NPStringConstants.COMMIT;
import static com.io7m.northpike.strings.NPStringConstants.ERROR_NONEXISTENT;
import static com.io7m.northpike.strings.NPStringConstants.REPOSITORY;
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
  private final LinkedBlockingQueue<NPRepositoryCommandType<?>> commands;
  private final NPTelemetryServiceType telemetry;
  private final List<? extends NPSCMRepositoryFactoryType> scmFactories;
  private final NPStrings strings;
  private final ConcurrentHashMap<NPRepositoryID, NPSCMRepositoryType> repositories;
  private final NPServerDirectoryConfiguration directories;

  private NPRepositoryService(
    final RPServiceDirectoryType inServices,
    final CloseableCollectionType<NPServerException> inResources,
    final ExecutorService inMainExecutor,
    final NPEventServiceType inEvents,
    final NPDatabaseType inDatabase,
    final NPTelemetryServiceType inTelemetry,
    final List<? extends NPSCMRepositoryFactoryType> inScmFactories,
    final NPStrings inStrings,
    final NPServerDirectoryConfiguration inDirectories)
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
    this.directories =
      Objects.requireNonNull(inDirectories, "directories");
    this.closed =
      new AtomicBoolean(true);
    this.future =
      new CompletableFuture<>();
    this.commands =
      new LinkedBlockingQueue<>();
    this.repositories =
      new ConcurrentHashMap<>();
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
      resources.add(
        Executors.newThreadPerTaskExecutor(
          Thread.ofVirtual()
            .name("com.io7m.northpike.repository-", 0L)
            .factory()
        )
      );

    return new NPRepositoryService(
      services,
      resources,
      mainExecutor,
      events,
      database,
      telemetry,
      scmFactories,
      strings,
      configuration.directories()
    );
  }

  @Override
  public CompletableFuture<Void> start(
    final NPRepositoryStartup startup)
  {
    if (this.closed.compareAndSet(true, false)) {
      switch (startup) {
        case PERFORM_UPDATE_ALL_ON_STARTUP -> {
          this.commands.add(new CommandUpdateAll(new CompletableFuture<>()));
        }
        case PERFORM_NO_UPDATE_ON_STARTUP -> {
          // Nothing to do.
        }
      }
      this.mainExecutor.execute(this::run);
    }
    return this.future;
  }

  @Override
  public CompletableFuture<Void> update()
  {
    final var command = new CommandUpdateAll(new CompletableFuture<>());
    this.commands.add(command);
    return command.future;
  }

  @Override
  public CompletableFuture<Void> repositoryUpdate(
    final NPRepositoryID id)
  {
    Objects.requireNonNull(id, "id");

    final var command = new CommandUpdateOne(id, new CompletableFuture<>());
    this.commands.add(command);
    return command.future;
  }

  @Override
  public NPArchive commitCreateArchiveFor(
    final NPCommitID commit)
    throws InterruptedException, NPException
  {
    Objects.requireNonNull(commit, "commit");

    final var command =
      new CommandCreateArchive(commit, new CompletableFuture<>());
    this.commands.add(command);

    try {
      return command.future.get();
    } catch (final ExecutionException e) {
      throw NPException.ofException(e.getCause());
    }
  }

  @Override
  public NPFingerprint commitSignatureVerify(
    final NPCommitID commit,
    final NPSignatureKeyLookupType keyLookup)
    throws NPException, InterruptedException
  {
    Objects.requireNonNull(commit, "commit");
    Objects.requireNonNull(keyLookup, "keyLookup");

    final var command =
      new CommandVerifyCommit(keyLookup, commit, new CompletableFuture<>());
    this.commands.add(command);

    try {
      return command.future.get();
    } catch (final ExecutionException e) {
      throw NPException.ofException(e.getCause());
    }
  }

  @Override
  public boolean repositoryHasPublicKeyAssigned(
    final NPRepositoryID repository,
    final NPFingerprint fingerprint)
    throws NPException
  {
    Objects.requireNonNull(repository, "repository");
    Objects.requireNonNull(fingerprint, "fingerprint");

    return this.timed("RepositoryHasPublicKeyAssigned", () -> {
      try (var connection =
             this.database.openConnection(NORTHPIKE)) {
        try (var transaction =
               connection.openTransaction()) {
          return transaction.queries(RepositoryPublicKeyIsAssignedType.class)
            .execute(
              new RepositoryPublicKeyIsAssignedType.Parameters(
                repository,
                fingerprint
              )
            );
        }
      }
    }).booleanValue();
  }

  @Override
  public NPRepositorySigningPolicy repositorySigningPolicyFor(
    final NPRepositoryID repository)
    throws NPException
  {
    Objects.requireNonNull(repository, "repository");

    return this.timed("RepositorySigningPolicyFor", () -> {
      return this.repositoryGet(repository)
        .orElseThrow(() -> this.errorNonexistentRepository(repository))
        .signingPolicy();
    });
  }

  @Override
  public NPCommit commitGet(
    final NPCommitID commitID)
    throws NPException
  {
    Objects.requireNonNull(commitID, "commitID");

    return this.timed("CommitGet", () -> {
      try (var connection =
             this.database.openConnection(NORTHPIKE_READ_ONLY)) {
        try (var transaction =
               connection.openTransaction()) {
          return transaction.queries(RepositoryCommitGetType.class)
            .execute(commitID)
            .orElseThrow(() -> this.errorNonexistentCommit(commitID));
        }
      }
    });
  }

  @Override
  public Optional<NPRepositoryDescription> repositoryGet(
    final NPRepositoryID repository)
    throws NPException
  {
    Objects.requireNonNull(repository, "repository");

    return this.timed("RepositoryGet", () -> {
      try (var connection =
             this.database.openConnection(NORTHPIKE_READ_ONLY)) {
        try (var transaction =
               connection.openTransaction()) {
          return transaction.queries(RepositoryGetType.class)
            .execute(repository);
        }
      }
    });
  }

  @Override
  public void repositoryPut(
    final NPAuditOwnerType user,
    final NPRepositoryDescription repository)
    throws NPException
  {
    Objects.requireNonNull(user, "user");
    Objects.requireNonNull(repository, "repository");

    this.timed("RepositoryCreate", () -> {
      try (var connection =
             this.database.openConnection(NORTHPIKE)) {
        try (var transaction =
               connection.openTransaction()) {
          transaction.setOwner(user);
          transaction.queries(RepositoryPutType.class).execute(repository);
          transaction.commit();
        }
      }

      this.commands.add(
        new CommandUpdateOne(repository.id(), new CompletableFuture<>())
      );
      return Void.class;
    });
  }

  @Override
  public void repositoryPublicKeyAssign(
    final NPAuditOwnerType user,
    final NPRepositoryID repository,
    final NPFingerprint key)
    throws NPException
  {
    Objects.requireNonNull(user, "user");
    Objects.requireNonNull(repository, "repository");
    Objects.requireNonNull(key, "key");

    this.timed("RepositoryPublicKeyAssign", () -> {
      try (var connection =
             this.database.openConnection(NORTHPIKE)) {
        try (var transaction =
               connection.openTransaction()) {
          transaction.setOwner(user);
          transaction.queries(RepositoryPublicKeyAssignType.class)
            .execute(
              new RepositoryPublicKeyAssignType.Parameters(repository, key)
            );
          transaction.commit();
        }
      }
      return Void.class;
    });
  }

  private void run()
  {
    LOG.info("Starting Repository service");

    this.events.emit(new NPRepositoryServiceStarted());
    this.future.complete(null);

    while (!this.closed.get()) {
      NPRepositoryCommandType<?> command = null;
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

  private interface PartialProcedureType<T, E extends Exception>
  {
    T execute() throws E;
  }

  private <T, E extends Exception> T timed(
    final String operation,
    final PartialProcedureType<T, E> proc)
    throws E
  {
    final var span =
      this.telemetry.tracer()
        .spanBuilder(operation)
        .startSpan();

    try (var ignored = span.makeCurrent()) {
      return proc.execute();
    } catch (final Throwable e) {
      recordSpanException(e);
      throw e;
    } finally {
      span.end();
    }
  }

  private void processCommandTimed(
    final NPRepositoryCommandType<?> command)
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
    final NPRepositoryCommandType<?> command)
  {
    switch (command) {
      case final CommandUpdateAll c -> {
        this.processCommandUpdateAll(c);
        return;
      }
      case final CommandCreateArchive c -> {
        this.processCommandCreateArchive(c);
        return;
      }
      case final CommandVerifyCommit c -> {
        this.processCommandVerifyCommit(c);
        return;
      }
      case final CommandUpdateOne c -> {
        this.processCommandUpdateOne(c);
        return;
      }
    }
  }

  private NPServerException errorNonexistentCommit(
    final NPCommitID commitID)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(COMMIT),
          commitID.commitId().value()
        ),
        Map.entry(
          this.strings.format(REPOSITORY),
          commitID.repository().value().toString()
        )
      ),
      Optional.empty()
    );
  }

  private NPServerException errorNonexistentRepository(
    final NPRepositoryID id)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(REPOSITORY),
          id.toString()
        )
      ),
      Optional.empty()
    );
  }

  private void processCommandVerifyCommit(
    final CommandVerifyCommit verifyCommit)
  {
    try {
      final var repository =
        this.openOrGetRepository(verifyCommit.commit.repository());

      final NPFingerprint fingerprint =
        repository.commitVerifySignature(
          verifyCommit.commit.commitId(),
          verifyCommit.keyLookup()
        );

      verifyCommit.future.complete(fingerprint);
    } catch (final Throwable e) {
      verifyCommit.future.completeExceptionally(e);
    }
  }

  private void processCommandCreateArchive(
    final CommandCreateArchive createArchive)
  {
    try {
      final var repository =
        this.archiveCreateSetupRepository(createArchive);

      final var archive =
        this.archiveCreateFile(createArchive, repository);

      this.archiveSaveInDatabase(archive);
      createArchive.future.complete(archive);
    } catch (final Throwable e) {
      createArchive.future.completeExceptionally(e);
    }
  }

  private void archiveSaveInDatabase(
    final NPArchive archive)
    throws NPDatabaseException
  {
    try (var connection = this.database.openConnection(NORTHPIKE)) {
      try (var transaction = connection.openTransaction()) {
        transaction.queries(ArchivePutType.class)
          .execute(archive);
        transaction.commit();
      }
    }
  }

  private NPArchive archiveCreateFile(
    final CommandCreateArchive createArchive,
    final NPSCMRepositoryType repository)
    throws NoSuchAlgorithmException, NPSCMRepositoryException
  {
    final var token =
      NPToken.generate();

    final var outputFile =
      this.directories.archiveDirectory()
        .resolve(NPArchive.fileNameFor(token));
    final var outputFileTmp =
      this.directories.archiveDirectory()
        .resolve(NPArchive.fileNameForTemporary(token));
    final var checksumOutputFile =
      this.directories.archiveDirectory()
        .resolve(NPArchive.checksumFileNameFor(token));
    final var checksumOutputFileTmp =
      this.directories.archiveDirectory()
        .resolve(NPArchive.checksumFileNameForTemporary(token));

    final var archive =
      repository.commitArchive(
        createArchive.commit,
        token,
        outputFile,
        outputFileTmp,
        checksumOutputFile,
        checksumOutputFileTmp
      );

    final var description = repository.description();
    this.events.emit(new NPRepositoryArchiveCreated(
      description.id(),
      description.url(),
      description.provider(),
      outputFile
    ));
    return archive;
  }

  private NPSCMRepositoryType archiveCreateSetupRepository(
    final CommandCreateArchive createArchive)
    throws NPDatabaseException, NPServerException
  {
    return this.openOrGetRepository(createArchive.commit.repository());
  }

  private NPSCMRepositoryType openOrGetRepository(
    final NPRepositoryID repositoryId)
    throws NPDatabaseException, NPServerException
  {
    final var repositoryDescriptions =
      this.repositoriesLoadDescriptions();
    final var repositoryDescription =
      repositoryDescriptions.get(repositoryId);

    if (repositoryDescription == null) {
      throw this.errorNoSuchRepository(repositoryId);
    }

    final var repository =
      this.repositoryOpen(repositoryDescription);

    this.repositoryUpdate(repository);
    return repository;
  }

  private NPServerException errorNoSuchRepository(
    final NPRepositoryID repositoryId)
  {
    return new NPServerException(
      this.strings.format(ERROR_NONEXISTENT),
      errorNonexistent(),
      Map.ofEntries(
        Map.entry(
          this.strings.format(REPOSITORY),
          repositoryId.toString()
        )
      ),
      Optional.empty()
    );
  }

  private void processCommandUpdateOne(
    final CommandUpdateOne command)
  {
    try {
      Span.current()
        .setAttribute("RepositoryID", command.id.toString());

      this.repositoriesReloadConfigurations();

      final var existing =
        this.repositories.get(command.id);

      if (existing == null) {
        throw this.errorNoSuchRepository(command.id);
      }

      Span.current()
        .setAttribute("RepositoryURI", existing.description().url().toString());

      this.repositoryUpdate(existing);
    } catch (final Throwable e) {
      command.future.completeExceptionally(e);
    } finally {
      command.future.complete(null);
    }
  }

  private void processCommandUpdateAll(
    final CommandUpdateAll check)
  {
    try {
      this.repositoriesReloadConfigurations();
      this.repositoriesUpdateAll();

    } catch (final Throwable e) {
      check.future.completeExceptionally(e);
    } finally {
      check.future.complete(null);
    }
  }

  private void repositoriesReloadConfigurations()
    throws NPDatabaseException
  {
    final var repositoryDescriptions =
      this.repositoriesLoadDescriptions();

    this.repositoriesOpenAll(repositoryDescriptions);
    this.repositoriesRemoveUnused(repositoryDescriptions);
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
    final var description =
      repository.description();

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
            transaction.queries(RepositoryCommitsGetMostRecentlyReceivedType.class)
              .execute(repository.description().id())
              .map(NPCommitSummary::timeReceived);

          final var commits =
            repository.commitsSinceTime(since);

          commitCount =
            Integer.toUnsignedLong(commits.commits().size());

          transaction.queries(RepositoryCommitsPutType.class)
            .execute(new Parameters(
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
    final HashMap<NPRepositoryID, NPRepositoryDescription> repositoryDescriptions)
  {
    final var remove = new HashSet<NPRepositoryID>();

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
    final NPRepositoryID id)
  {
    LOG.debug("Deleting repository {}", id);

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

  private void repositoriesOpenAll(
    final HashMap<NPRepositoryID, NPRepositoryDescription> repositoryDescriptions)
  {
    for (final var description : repositoryDescriptions.values()) {
      try {
        this.repositoryOpen(description);
      } catch (final NPServerException e) {
        // Ignore here
      }
    }
  }

  private NPSCMRepositoryType repositoryOpen(
    final NPRepositoryDescription description)
    throws NPServerException
  {
    final var existing =
      this.repositories.get(description.id());

    if (existing != null) {
      return existing;
    }

    LOG.debug(
      "Opening repository {} ({})",
      description.id(),
      description.url()
    );

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
          this.directories.repositoryDirectory(),
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
      return scm;
    } catch (final NPServerException e) {
      recordSpanException(e);
      this.events.emit(new NPRepositoryConfigureFailed(
        description.id(),
        description.url(),
        description.provider(),
        e
      ));
      throw e;
    }
  }

  private HashMap<NPRepositoryID, NPRepositoryDescription> repositoriesLoadDescriptions()
    throws NPDatabaseException
  {
    final var descriptions =
      new HashMap<NPRepositoryID, NPRepositoryDescription>();

    try (var connection = this.database.openConnection(NORTHPIKE_READ_ONLY)) {
      try (var transaction = connection.openTransaction()) {
        final var list =
          transaction.queries(RepositoryListType.class);
        final var paged =
          list.execute(NPDatabaseUnit.UNIT);
        final var pageInitial =
          paged.pageCurrent(transaction);

        final var pageCount = pageInitial.pageCount();
        for (var pageIndex = pageInitial.pageIndex(); pageIndex <= pageCount; ++pageIndex) {
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
      LOG.debug("Shutting down repository service.");
      this.future.complete(null);
      this.resources.close();
    }
  }

  private sealed interface NPRepositoryCommandType<R>
  {
    CompletableFuture<R> future();
  }

  record CommandUpdateAll(
    CompletableFuture<Void> future)
    implements NPRepositoryCommandType<Void>
  {

  }

  record CommandCreateArchive(
    NPCommitID commit,
    CompletableFuture<NPArchive> future)
    implements NPRepositoryCommandType<NPArchive>
  {

  }

  record CommandVerifyCommit(
    NPSignatureKeyLookupType keyLookup,
    NPCommitID commit,
    CompletableFuture<NPFingerprint> future)
    implements NPRepositoryCommandType<NPFingerprint>
  {

  }

  record CommandUpdateOne(
    NPRepositoryID id,
    CompletableFuture<Void> future)
    implements NPRepositoryCommandType<Void>
  {

  }
}
