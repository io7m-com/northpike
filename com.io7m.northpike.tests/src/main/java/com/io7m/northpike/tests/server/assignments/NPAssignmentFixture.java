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


package com.io7m.northpike.tests.server.assignments;

import com.io7m.northpike.assignments.NPAssignment;
import com.io7m.northpike.assignments.NPAssignmentName;
import com.io7m.northpike.database.api.NPDatabaseConnectionType;
import com.io7m.northpike.database.api.NPDatabaseQueriesAssignmentsType;
import com.io7m.northpike.database.api.NPDatabaseQueriesPlansType;
import com.io7m.northpike.database.api.NPDatabaseQueriesRepositoriesType;
import com.io7m.northpike.database.api.NPDatabaseQueriesSCMProvidersType;
import com.io7m.northpike.database.api.NPDatabaseTransactionType;
import com.io7m.northpike.database.api.NPDatabaseType;
import com.io7m.northpike.model.NPArchive;
import com.io7m.northpike.model.NPCommit;
import com.io7m.northpike.model.NPCommitID;
import com.io7m.northpike.model.NPCommitSummary;
import com.io7m.northpike.model.NPHash;
import com.io7m.northpike.model.NPRepositoryCredentialsNone;
import com.io7m.northpike.model.NPRepositoryDescription;
import com.io7m.northpike.model.NPSCMProviderDescription;
import com.io7m.northpike.model.NPToken;
import com.io7m.northpike.plans.NPPlanType;
import com.io7m.northpike.plans.parsers.NPPlanParserFactoryType;
import com.io7m.northpike.plans.parsers.NPPlanParsers;
import com.io7m.northpike.plans.parsers.NPPlanSerializers;
import com.io7m.northpike.repository.jgit.NPSCMRepositoriesJGit;
import com.io7m.northpike.scm_repository.spi.NPSCMRepositoryType;
import com.io7m.northpike.server.internal.agents.NPAgentServiceType;
import com.io7m.northpike.server.internal.archives.NPArchiveServiceType;
import com.io7m.northpike.server.internal.clock.NPClock;
import com.io7m.northpike.server.internal.clock.NPClockServiceType;
import com.io7m.northpike.server.internal.events.NPEventService;
import com.io7m.northpike.server.internal.repositories.NPRepositoryServiceType;
import com.io7m.northpike.server.internal.telemetry.NPTelemetryNoOp;
import com.io7m.northpike.strings.NPStrings;
import com.io7m.northpike.telemetry.api.NPEventServiceType;
import com.io7m.northpike.telemetry.api.NPEventType;
import com.io7m.northpike.telemetry.api.NPTelemetryServiceType;
import com.io7m.northpike.tests.NPEventInterceptingService;
import com.io7m.northpike.tests.containers.NPTestContainers;
import com.io7m.northpike.toolexec.NPTXParserFactoryType;
import com.io7m.northpike.toolexec.NPTXParsers;
import com.io7m.repetoir.core.RPServiceDirectory;
import com.io7m.repetoir.core.RPServiceDirectoryType;
import com.io7m.zelador.test_extension.CloseableResourcesType;
import org.mockito.Mockito;

import java.net.URI;
import java.nio.file.Path;
import java.time.Clock;
import java.time.OffsetDateTime;
import java.util.Comparator;
import java.util.Locale;
import java.util.Objects;
import java.util.Queue;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;

import static com.io7m.northpike.database.api.NPDatabaseRole.NORTHPIKE;
import static com.io7m.northpike.tests.scm_repository.NPSCMRepositoriesJGitTest.unpack;
import static org.mockito.ArgumentMatchers.any;

public final class NPAssignmentFixture implements AutoCloseable
{
  private final NPTestContainers.NPDatabaseFixture dbFixture;
  private final URI reposSource;
  private final NPSCMRepositoriesJGit repositoryProvider;
  private final NPRepositoryDescription repositoryDescription;
  private final NPSCMRepositoryType repository;
  private NPCommit commitHead;
  private RPServiceDirectory services;
  private NPDatabaseType database;
  private NPDatabaseConnectionType connection;
  private NPDatabaseTransactionType transaction;
  private NPAssignment assignment;
  private NPEventInterceptingService events;
  private NPAgentServiceType mockAgentService;
  private NPArchiveServiceType mockArchiveService;

  private NPAssignmentFixture(
    final NPTestContainers.NPDatabaseFixture inDbFixture,
    final URI inReposSource,
    final NPSCMRepositoriesJGit inRepositoryProvider,
    final NPRepositoryDescription inRepositoryDescription,
    final NPSCMRepositoryType inRepository)
  {
    this.dbFixture =
      Objects.requireNonNull(inDbFixture, "fixture");
    this.reposSource =
      Objects.requireNonNull(inReposSource, "reposSource");
    this.repositoryProvider =
      Objects.requireNonNull(inRepositoryProvider, "repositoryProvider");
    this.repositoryDescription =
      Objects.requireNonNull(inRepositoryDescription, "repositoryDescription");
    this.repository =
      Objects.requireNonNull(inRepository, "repository");
  }

  public static NPAssignmentFixture create(
    final NPTestContainers.NPDatabaseFixture databaseFixture,
    final Path reposDirectory)
    throws Exception
  {
    final var reposSource =
      unpack("example.git.tar", reposDirectory);

    final var repositoryProvider =
      new NPSCMRepositoriesJGit();

    final var repositoryDescription =
      new NPRepositoryDescription(
        NPSCMRepositoriesJGit.providerNameGet(),
        UUID.randomUUID(),
        reposSource,
        NPRepositoryCredentialsNone.CREDENTIALS_NONE
      );

    final var tmpServices =
      new RPServiceDirectory();
    tmpServices.register(
      NPStrings.class, NPStrings.create(Locale.ROOT));
    tmpServices.register(
      NPTelemetryServiceType.class, NPTelemetryNoOp.noop());

    final var repository =
      repositoryProvider.createRepository(
        tmpServices,
        reposDirectory,
        repositoryDescription
      );

    return new NPAssignmentFixture(
      databaseFixture,
      reposSource,
      repositoryProvider,
      repositoryDescription,
      repository
    );
  }

  public NPDatabaseType database()
  {
    return this.database;
  }

  public NPDatabaseConnectionType connection()
  {
    return this.connection;
  }

  public NPDatabaseTransactionType transaction()
  {
    return this.transaction;
  }

  public NPEventInterceptingService eventService()
  {
    return this.events;
  }

  public void reset(
    final CloseableResourcesType closeables)
    throws Exception
  {
    this.dbFixture.reset();

    if (this.services != null) {
      this.services.close();
    }
    this.services = new RPServiceDirectory();

    final var clock =
      new NPClock(Clock.systemUTC());
    this.events =
      new NPEventInterceptingService(
        NPEventService.create(NPTelemetryNoOp.noop())
      );
    this.mockAgentService =
      Mockito.mock(NPAgentServiceType.class);
    this.mockArchiveService =
      Mockito.mock(NPArchiveServiceType.class);
    final var repositories =
      Mockito.mock(NPRepositoryServiceType.class);

    this.database =
      closeables.addPerTestResource(this.dbFixture.createDatabase());
    this.connection =
      closeables.addPerTestResource(this.database.openConnection(NORTHPIKE));
    this.transaction =
      closeables.addPerTestResource(this.connection.openTransaction());

    this.services.register(
      NPTelemetryServiceType.class, NPTelemetryNoOp.noop());
    this.services.register(
      NPStrings.class, NPStrings.create(Locale.ROOT));
    this.services.register(
      NPDatabaseType.class, this.database);
    this.services.register(
      NPClockServiceType.class, clock);
    this.services.register(
      NPEventServiceType.class, this.events);
    this.services.register(
      NPAgentServiceType.class, this.mockAgentService);
    this.services.register(
      NPArchiveServiceType.class, this.mockArchiveService);
    this.services.register(
      NPRepositoryServiceType.class, repositories);
    this.services.register(
      NPPlanParserFactoryType.class, new NPPlanParsers());
    this.services.register(
      NPTXParserFactoryType.class, new NPTXParsers());

    this.transaction.queries(NPDatabaseQueriesSCMProvidersType.PutType.class)
      .execute(new NPSCMProviderDescription(
        this.repositoryDescription.provider(),
        "Git",
        URI.create("https://www.git-scm.com")
      ));

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.PutType.class)
      .execute(this.repositoryDescription);

    final var since =
      this.transaction.queries(NPDatabaseQueriesRepositoriesType.CommitsGetMostRecentlyReceivedType.class)
        .execute(this.repositoryDescription.id())
        .map(NPCommitSummary::timeReceived);

    final var commits =
      this.repository.commitsSinceTime(since);

    this.commitHead =
      commits.commits()
        .stream()
        .max(Comparator.comparing(NPCommit::timeCreated))
        .orElseThrow();

    this.transaction.queries(NPDatabaseQueriesRepositoriesType.CommitsPutType.class)
      .execute(new NPDatabaseQueriesRepositoriesType.CommitsPutType.Parameters(
        commits.commits(),
        commits.commitGraph()
      ));

    this.transaction.commit();

    Mockito.when(repositories.createArchiveFor(any()))
      .thenReturn(CompletableFuture.completedFuture(
        new NPArchive(
          NPToken.generate(),
          this.commitHead.id(),
          new NPHash(
            "SHA-256",
            "a939645e193074c683dd7132c65a5571e8fdb59d67cbe1c17ff7c29b5289647c"
          ),
          OffsetDateTime.now()
        )
      ));
  }

  @Override
  public void close()
    throws Exception
  {
    if (this.services != null) {
      this.services.close();
    }
  }

  public NPArchiveServiceType mockArchiveService()
  {
    return this.mockArchiveService;
  }

  public NPAgentServiceType mockAgentService()
  {
    return this.mockAgentService;
  }

  public NPAssignment createAssignmentWithPlan(
    final NPPlanType plan)
    throws Exception
  {
    this.transaction.queries(NPDatabaseQueriesPlansType.PutType.class)
      .execute(new NPDatabaseQueriesPlansType.PutType.Parameters(
        plan,
        new NPPlanSerializers()
      ));

    this.assignment =
      new NPAssignment(
        NPAssignmentName.of("com.io7m.a1"),
        this.repositoryDescription.id(),
        plan.identifier()
      );

    this.transaction.queries(NPDatabaseQueriesAssignmentsType.PutType.class)
      .execute(this.assignment);

    this.transaction.commit();
    return this.assignment;
  }

  public RPServiceDirectoryType services()
  {
    return this.services;
  }

  public NPCommitID commit()
  {
    return this.commitHead.id();
  }

  public Queue<NPEventType> events()
  {
    return this.events.eventQueue();
  }
}
